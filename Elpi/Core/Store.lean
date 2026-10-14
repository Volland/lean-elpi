import Lean.Data.PersistentHashMap
import Lean.Data.PersistentArray
import Elpi.Core.Term
import Elpi.Core.Constraints

/-!
# Persistent substitution

Persistent uvar substitution and the `Backtrackable` host-monad class. The store is an
immutable, structurally shared value, so a choice point keeps the `Store` it was created
with and backtracking is a pointer swap.
-/

-- @lat: [[components#Persistent substitution]]

namespace Elpi

structure UVarInfo where
  /-- Scope level ℓ: the assignment may only mention levels `< ℓ`. -/
  level : Nat
  name? : Option String := none
  deriving Inhabited

-- @tg: implements:: [[openspec:elpi-core-engine#Persistent store]]
structure Store where
  assign  : Lean.PersistentHashMap UVarId Term := {}
  info    : Lean.PersistentArray UVarInfo := {}
  nextVar : Nat := 0
  cstore  : ConstraintStore := {}
  /-- Constraints woken by assignments, oldest last (id, variable). -/
  wakeQueue : List (Nat × UVarId) := []
  /-- Variables with an index below this are frozen (CHR matching and guards). -/
  protect : Nat := 0
  hooks : Array UnifHook := #[]
  /-- Constants (by index) that hooks treat as interpreted. -/
  interp : Array Nat := #[]
  /-- Print names (`X0`, `X1`, …) handed out so far to unassigned variables. -/
  names   : Lean.PersistentHashMap UVarId Nat := {}
  nameCount : Nat := 0
  deriving Inhabited

namespace Store

/-- Fresh unification variable at scope level `lvl`. -/
def fresh (s : Store) (lvl : Nat) (name? : Option String := none) : UVarId × Store :=
  let u := UVarId.mk s.nextVar
  (u, { s with info := s.info.push { level := lvl, name? }, nextVar := s.nextVar + 1 })

def levelOf (s : Store) (u : UVarId) : Nat := (s.info.get! u.idx).level

def nameOf (s : Store) (u : UVarId) : Option String := (s.info.get! u.idx).name?

def lookup? (s : Store) (u : UVarId) : Option Term := s.assign.find? u

/-- Assign `u := t`, where `t` is a closed term at `u`'s level. -/
def setAssign (s : Store) (u : UVarId) (t : Term) : Store :=
  let woken := s.cstore.wake u
  { s with assign := s.assign.insert u t,
           wakeQueue := woken.foldl (init := s.wakeQueue) fun q id => (id, u) :: q }

def isAssigned (s : Store) (u : UVarId) : Bool := s.assign.contains u

/-- Dereference the head of `t` at depth `d`: replace an assigned `uvar` by its value
applied to its spine (β-reducing), repeatedly. Arguments are not normalised. -/
partial def deref (s : Store) (t : Term) (d : Nat) : Term :=
  match t with
  | .uvar u args =>
    match s.assign.find? u with
    | none => t
    | some v =>
      let ℓ := s.levelOf u
      let v := v.shiftUp ℓ (d - ℓ)
      deref s (Term.applyAt v args d) d
  | _ => t

/-- Fully normalise `t` at depth `d`: dereference every assigned variable. -/
partial def zonk (s : Store) (t : Term) (d : Nat) : Term :=
  match deref s t d with
  | .app h as => .app (zonk s h d) (as.map (zonk s · d))
  | .lam b => .lam (zonk s b (d + 1))
  | .uvar u as => .uvar u (as.map (zonk s · d))
  | .cvar i as => .cvar i (as.map (zonk s · d))
  | t => t

end Store

/-- Host monad state snapshots, complementing the persistent store. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Monad-generic engine]]
class Backtrackable (m : Type → Type) (σ : outParam Type) where
  save    : m σ
  restore : σ → m Unit

instance : Backtrackable Id Unit := ⟨pure (), fun _ => pure ()⟩
instance {ρ : Type} : Backtrackable (StateM ρ) ρ := ⟨get, set⟩
instance : Backtrackable IO Unit := ⟨pure (), fun _ => pure ()⟩

end Elpi
