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
  /-- Value of each unification variable, by index; `none` while unassigned. Updated in place
  when the store is not shared; backtracking undoes the writes through `trail`. -/
  assign  : Array (Option Term) := #[]
  info    : Array UVarInfo := #[]
  nextVar : Nat := 0
  /-- Indices of the variables assigned since the oldest live checkpoint, newest last. -/
  trail   : Array Nat := #[]
  /-- Assignments to variables below this index are trailed: a choice point or an attempt may
  have to undo them. Variables at or above it are discarded wholesale when it is undone. -/
  floor   : Nat := 0
  /-- In a checkpoint only: the length of `trail` when the checkpoint was taken. -/
  trailMark : Nat := 0
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
  let assign := s.assign
  let info := s.info
  let nv := s.nextVar
  -- release the store's own references so the arrays are updated in place when unshared
  let s := { s with assign := #[], info := #[] }
  (u, { s with assign := assign.push none, info := info.push { level := lvl, name? }, nextVar := nv + 1 })

def levelOf (s : Store) (u : UVarId) : Nat := (s.info[u.idx]!).level

def nameOf (s : Store) (u : UVarId) : Option String := (s.info[u.idx]!).name?

@[inline] def lookup? (s : Store) (u : UVarId) : Option Term :=
  if h : u.idx < s.assign.size then s.assign[u.idx] else none

/-- Assign `u := t`, where `t` is a closed term at `u`'s level. -/
def setAssign (s : Store) (u : UVarId) (t : Term) : Store :=
  let woken := s.cstore.wake u
  let wq := woken.foldl (init := s.wakeQueue) fun q id => (id, u) :: q
  let assign := s.assign
  let trail := s.trail
  let s := { s with assign := #[], trail := #[] }
  let trail := if u.idx < s.floor then trail.push u.idx else trail
  { s with assign := assign.set! u.idx (some t), trail, wakeQueue := wq }

def isAssigned (s : Store) (u : UVarId) : Bool := (s.lookup? u).isSome

/-! ### Checkpoints and undo

A choice point does not keep the store: it keeps a `checkpoint`, which drops the large arrays
and records the trail length, the variable count and the persistent fields (constraints, wake
queue, names). `undo` brings the live store back to a checkpoint by resetting the trailed
variables and truncating the arrays. -/

/-- Snapshot for backtracking: all small fields, none of the arrays. -/
def checkpoint (s : Store) : Store :=
  { s with assign := #[], info := #[], trail := #[], trailMark := s.trail.size }

/-- Start recording every assignment to an existing variable (a choice point or an attempt
that may fail is about to begin). Take the `checkpoint` first. -/
def track (s : Store) : Store := { s with floor := s.nextVar }

private partial def undoTrail (assign : Array (Option Term)) (trail : Array Nat) (mark : Nat) :
    Array (Option Term) × Array Nat :=
  if trail.size ≤ mark then (assign, trail) else
  let i := trail.back!
  let assign := if i < assign.size then assign.set! i none else assign
  undoTrail assign trail.pop mark

/-- Undo everything done to `cur` since the checkpoint `m` was taken from it. -/
def undo (cur : Store) (m : Store) : Store :=
  let assign := cur.assign
  let info := cur.info
  let trail := cur.trail
  -- `cur` is dead from here on, so the arrays are unshared whenever `cur` was
  let (assign, trail) := undoTrail assign trail m.trailMark
  { m with assign := assign.shrink m.nextVar, info := info.shrink m.nextVar, trail }

/-- An attempt that began with `checkpoint` `m` succeeded without leaving a choice point:
drop its trail entries except those an enclosing choice point (floor `m.floor`) still needs. -/
def settle (s : Store) (m : Store) : Store :=
  let trail := s.trail
  let s := { s with trail := #[] }
  let trail :=
    if m.floor == 0 then trail.shrink m.trailMark
    else Id.run do
      let mut trail := trail
      let mut w := m.trailMark
      for j in [m.trailMark:trail.size] do
        let i := trail[j]!
        if i < m.floor then
          trail := trail.set! w i
          w := w + 1
      return trail.shrink w
  { s with trail, floor := m.floor }

/-- Dereference the head of `t` at depth `d`: replace an assigned `uvar` by its value
applied to its spine (β-reducing), repeatedly. Arguments are not normalised. -/
partial def deref (s : Store) (t : Term) (d : Nat) : Term :=
  match t with
  | .uvar u args =>
    match s.lookup? u with
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
