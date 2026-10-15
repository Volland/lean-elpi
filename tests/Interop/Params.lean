import TestUtil
import Lean
open Elpi TestUtil Lean

inductive Typ where
  | base
  | arr (a b : Typ)
  deriving Elpi

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (a : α) (r : Tree α)
  deriving Elpi

structure Box (α β : Type) where
  fst : α
  rest : List (Option β)
  deriving Elpi

inductive Rose (α : Type) where
  | mk (a : α) (kids : List (Rose α))
  deriving Elpi

-- @tg: verifies:: [[openspec:lean-interop#Parametric and recursive deriving#Recursive type derives]]
#eval show CoreM Unit from do
  let ds := derivedSignatures (← getEnv)
  check (ds.contains "type arr typ -> typ -> typ.") s!"{ds}"
  let t := Typ.arr .base (.arr .base .base)
  match (fromElpi (toElpi t) : Except DecodeError Typ) with
  | .ok (.arr .base (.arr .base .base)) => pure ()
  | _ => throwError "decoded value differs"

-- @tg: verifies:: [[openspec:lean-interop#Parametric and recursive deriving#Parameters become type variables]]
#eval show CoreM Unit from do
  let ds := derivedSignatures (← getEnv)
  check (ds.contains "kind tree type -> type.") s!"{ds}"
  check (ds.contains "type leaf tree A.") s!"{ds}"
  check (ds.contains "type node tree A -> A -> tree A -> tree A.") s!"{ds}"
  check (ds.contains "kind box type -> type -> type.") s!"{ds}"
  check (ds.contains "type box.mk A -> list (option B) -> box A B.") s!"{ds}"
  check (ds.contains "type mk A -> list (rose A) -> rose A.") s!"{ds}"

-- @tg: verifies:: [[openspec:lean-interop#Parametric and recursive deriving#Instantiated instance round-trips]]
#eval show CoreM Unit from do
  let t : Tree Nat := .node .leaf 3 (.node .leaf 4 .leaf)
  match (fromElpi (toElpi t) : Except DecodeError (Tree Nat)) with
  | .ok (.node .leaf 3 (.node .leaf 4 .leaf)) => pure ()
  | _ => throwError "tree did not round-trip"
  let r : Rose String := .mk "a" [.mk "b" [], .mk "c" []]
  match (fromElpi (toElpi r) : Except DecodeError (Rose String)) with
  | .ok (.mk "a" [.mk "b" [], .mk "c" []]) => pure ()
  | _ => throwError "rose tree did not round-trip"
  -- a payload of the wrong type is a decoding error, not a crash
  match (fromElpi (toElpi (Tree.node .leaf "x" .leaf)) : Except DecodeError (Tree Nat)) with
  | .error _ => pure ()
  | .ok _ => throwError "a string payload decoded as a number"

-- @tg: verifies:: [[openspec:lean-interop#Parametric and recursive deriving#Indexed family is rejected]]
/-- error: deriving Elpi: Vec is an indexed family, which plain ELPI types cannot express (use the LF extension) -/
#guard_msgs in
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  deriving Elpi

-- @tg: verifies:: [[openspec:lean-interop#Signature inspection#Signature is shown]]
/-- info: kind tree type -> type.
type leaf tree A.
type node tree A -> A -> tree A -> tree A. -/
#guard_msgs in
#elpi_signature Tree
