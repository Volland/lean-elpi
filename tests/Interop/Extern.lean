import TestUtil
import Lean
open Elpi.Cmd Elpi TestUtil Lean

def twice (n : Nat) : Nat := 2 * n
elpi_extern twice

def half (n : Nat) : Option Nat := if n % 2 == 0 then some (n / 2) else none
elpi_extern partial half

def divisors (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d != 0 && n % d == 0
elpi_extern many divisors as "divisor"

def glue (xs ys : List Nat) (sep : String) : String := sep.intercalate ((xs ++ ys).map toString)
elpi_extern glue

inductive Tr (α : Type) where
  | leaf
  | node (l : Tr α) (a : α) (r : Tr α)
  deriving Elpi

def Tr.size {α : Type} : Tr α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size
def trSize (t : Tr Nat) : Nat := t.size
elpi_extern trSize as "tr-size"

elpi_program ex
elpi_accumulate ex lp%{ pred main-demo o:int. main-demo X :- twice 21 X. }%

#eval show CoreM Unit from do
  let env ← getEnv
  let names := (Registry.entries env).toList.map (·.name)
  check (names.contains "twice") s!"{names}"

-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Total function]]
#eval show MetaM Unit from do
  let s ← Elpi.query ex "twice 21 X"
  match s.head? with
  | some (.ok sol) => unless (sol.get? "X" : Option Nat) == some 42 do throwError "wrong value"
  | _ => throwError "no solution"
  let s ← Elpi.query ex "main-demo X"
  match s.head? with
  | some (.ok sol) => unless (sol.get? "X" : Option Nat) == some 42 do throwError "wrong value"
  | _ => throwError "no solution"

-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Partial function]]
#eval show MetaM Unit from do
  let s ← Elpi.query ex "half 10 X"
  match s.head? with
  | some (.ok sol) => unless (sol.get? "X" : Option Nat) == some 5 do throwError "wrong value"
  | _ => throwError "no solution"
  let f ← Elpi.query ex "half 7 X"
  unless f.head?.isNone do throwError "half 7 should fail"

-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Multi-valued function]]
#eval show MetaM Unit from do
  let s ← Elpi.query ex "divisor 12 D"
  let ds := (s.take 10).filterMap fun | .ok sol => (sol.get? "D" : Option Nat) | _ => none
  unless ds == [1, 2, 3, 4, 6, 12] do throwError "divisors: {ds}"

-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Arguments of derived types]]
#eval show MetaM Unit from do
  let s ← Elpi.query ex "glue [1, 2] [3] \"-\" S"
  match s.head? with
  | some (.ok sol) => unless (sol.get? "S" : Option String) == some "1-2-3" do throwError "wrong glue"
  | _ => throwError "no solution"
  let s ← Elpi.query ex "tr-size (node (node leaf 1 leaf) 2 leaf) N"
  match s.head? with
  | some (.ok sol) => unless (sol.get? "N" : Option Nat) == some 2 do throwError "wrong size"
  | _ => throwError "no solution"

-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Signature is checked by ELPI]]
#eval show MetaM Unit from do
  -- an argument of the wrong ELPI type is rejected by the ELPI type checker
  let s ← Elpi.query ex "twice \"x\" X"
  match s.head? with
  | some (.error _) => pure ()
  | _ => throwError "expected a type error"

def bad (f : Nat → Nat) : Nat := f 0
-- @tg: verifies:: [[openspec:lean-interop#Typed Lean externs#Unsupported type is rejected]]
/-- error: elpi_extern: no ToElpi instance for the field type Nat -> Nat -/
#guard_msgs in
elpi_extern bad
