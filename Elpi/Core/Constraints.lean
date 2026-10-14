import Lean.Data.PersistentHashMap
import Elpi.Core.Term

/-!
# Constraint store

Persistent store of delayed goals: constraints indexed by id, by the variables they are
suspended on (the wake index) and by predicate (the CHR partner index), plus the state of
native handlers. It is a field of the persistent `Store`, so choice points capture it and
backtracking restores it with no compensating code.
-/

-- @lat: [[components#Constraint store]]

namespace Elpi

/-- A clause added by `=>`: a clause term and the depth it was added at. -/
structure LocalClause where
  term : Term
  depth : Nat
  deriving Inhabited

/-- Hypothetical clauses, newest group first. -/
abbrev Locals := List LocalClause

/-- A suspended goal with the context it must resume in. -/
structure Constraint where
  id : Nat
  goal : Term
  /-- Unification variables the goal is suspended on. -/
  keys : Array UVarId
  /-- Scope level of the innermost `pi` it was created under. -/
  depth : Nat
  /-- Snapshot of the local program at that point. -/
  locals : Locals
  /-- Predicate of the goal, when it is a plain application. -/
  pred : Option ConstId
  /-- Name of the native handler that owns it. -/
  owner : Option String := none
  deriving Inhabited

-- @tg: implements:: [[openspec:elpi-constraints#Backtrackable constraint store]]
structure ConstraintStore where
  byId : Lean.PersistentHashMap Nat Constraint := {}
  byKey : Lean.PersistentHashMap UVarId (Array Nat) := {}
  byPred : Lean.PersistentHashMap Nat (Array Nat) := {}
  handlerState : Lean.PersistentHashMap String Dynamic := {}
  nextId : Nat := 0
  deriving Inhabited

namespace ConstraintStore

/-- Add a constraint (its `id` is assigned here); returns the stored constraint. -/
def add (cs : ConstraintStore) (c : Constraint) : Constraint × ConstraintStore :=
  let c := { c with id := cs.nextId }
  let byKey := c.keys.foldl (init := cs.byKey) fun m k =>
    m.insert k ((m.findD k #[]).push c.id)
  let byPred := match c.pred with
    | some p => cs.byPred.insert p.idx ((cs.byPred.findD p.idx #[]).push c.id)
    | none => cs.byPred
  (c, { cs with byId := cs.byId.insert c.id c, byKey, byPred, nextId := cs.nextId + 1 })

/-- Remove a constraint from every index. -/
def remove (cs : ConstraintStore) (id : Nat) : ConstraintStore :=
  match cs.byId.find? id with
  | none => cs
  | some c =>
    let byKey := c.keys.foldl (init := cs.byKey) fun m k =>
      m.insert k ((m.findD k #[]).filter (· != id))
    let byPred := match c.pred with
      | some p => cs.byPred.insert p.idx ((cs.byPred.findD p.idx #[]).filter (· != id))
      | none => cs.byPred
    { cs with byId := cs.byId.erase id, byKey, byPred }

/-- Ids suspended on a variable. -/
def wake (cs : ConstraintStore) (u : UVarId) : Array Nat := cs.byKey.findD u #[]

def find? (cs : ConstraintStore) (id : Nat) : Option Constraint := cs.byId.find? id

/-- All constraints, oldest first. -/
def toList (cs : ConstraintStore) : List Constraint :=
  (cs.byId.toList.map (·.2)).toArray.qsort (fun a b => a.id < b.id) |>.toList

def isEmpty (cs : ConstraintStore) : Bool := cs.byId.isEmpty

end ConstraintStore

/-! ### Tier T3: native constraint handlers -/

/-- Read-only view a handler gets: the constraints it owns (oldest first), its private
state and the current dereferencing function. -/
structure HStore where
  owned : List Constraint
  state : Dynamic
  deref : Term → Term

/-- Typed access to the handler's state. -/
def HStore.getState {α : Type} [TypeName α] (s : HStore) : Option α := s.state.get? α

inductive HandlerResult where
  /-- Replace the handler's constraints with the given set. -/
  | simplify (keep : List Constraint) (state? : Option Dynamic := none)
  /-- Keep the constraints and push the given goals. -/
  | propagate (goals : List Term) (state? : Option Dynamic := none)
  /-- Start backtracking. -/
  | fail
  /-- Store the constraint unchanged. -/
  | keep (state? : Option Dynamic := none)
  deriving Inhabited

-- @tg: implements:: [[openspec:elpi-solver-api#Native constraint handlers]]
structure ConstraintHandler where
  /-- ELPI predicate names the handler owns. -/
  keys : List String
  /-- Initial private state. -/
  init : Dynamic
  onAdd : Constraint → HStore → HandlerResult
  onWake : UVarId → HStore → HandlerResult

/-! ### Tier T4: unification hooks -/

inductive HookResult where
  /-- A substitution; the engine re-checks it for occurs and scope violations. -/
  | solved (subst : List (UVarId × Term))
  /-- Delay the problem as a goal keyed on its flexible variables. -/
  | suspend
  | fail
  /-- This hook has no opinion; the next one is consulted. -/
  | decline
  deriving Inhabited

-- @tg: implements:: [[openspec:elpi-solver-api#Unification hooks]]
structure UnifHook where
  /-- Symbols treated as interpreted: a rigid–rigid clash on one of them is `stuck`. -/
  interpreted : List String := []
  /-- Called with a dereferencing function, the two sides and the depth. -/
  onStuck : (Term → Term) → Term → Term → Nat → HookResult
  deriving Inhabited

end Elpi
