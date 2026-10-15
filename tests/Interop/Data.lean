import TestUtil
import Lean
open Elpi.Cmd Elpi TestUtil Lean

elpi_data lp%{
  kind shape type.
  type circle int -> shape.
  type square int -> shape.
  type beside shape -> shape -> shape.

  kind tree type -> type.
  type leaf tree A.
  type node tree A -> A -> tree A -> tree A.

  kind entry type.
  type entry.mk string -> list int -> option shape -> entry.
}%

-- @tg: verifies:: [[openspec:lean-interop#ELPI data types#Data becomes an inductive]]
#eval show CoreM Unit from do
  let s : Shape := .beside (.circle 1) (.square 2)
  match (fromElpi (toElpi s) : Except DecodeError Shape) with
  | .ok (.beside (.circle 1) (.square 2)) => pure ()
  | _ => throwError "shape did not round-trip"
  let t : Tree Int := .node .leaf (-3) .leaf
  match (fromElpi (toElpi t) : Except DecodeError (Tree Int)) with
  | .ok (.node .leaf (-3) .leaf) => pure ()
  | _ => throwError "tree did not round-trip"

-- @tg: verifies:: [[openspec:lean-interop#ELPI data types#Declarations are preserved]]
#eval show CoreM Unit from do
  let ds := derivedSignatures (← getEnv)
  check (ds.contains "kind shape type.") s!"{ds}"
  check (ds.contains "type beside shape -> shape -> shape.") s!"{ds}"
  check (ds.contains "type node tree A -> A -> tree A -> tree A.") s!"{ds}"

elpi_program areas
elpi_accumulate areas lp%{
  accumulate lean.
  pred area i:shape, o:int.
  area (circle R) A :- A is 3 * R * R.
  area (square S) A :- A is S * S.
  area (beside X Y) A :- area X A1, area Y A2, A is A1 + A2.

  pred mirror i:shape, o:shape.
  mirror (beside X Y) (beside Y1 X1) :- !, mirror X X1, mirror Y Y1.
  mirror S S.
}%

-- @tg: verifies:: [[openspec:lean-interop#ELPI data types#Program and Lean agree on the type]]
#eval show MetaM Unit from do
  let s ← Elpi.query areas "area (beside (circle 1) (square 2)) A"
  match s.head? with
  | some (.ok sol) =>
    unless (sol.get? "A" : Option Int) == some 7 do throwError "wrong area"
  | _ => throwError "no solution"
  let m ← Elpi.query areas "mirror (beside (circle 1) (square 2)) M"
  match m.head? with
  | some (.ok sol) =>
    match (sol.get? "M" : Option Shape) with
    | some (.beside (.square 2) (.circle 1)) => pure ()
    | _ => throwError "wrong mirror"
  | _ => throwError "no solution"

-- @tg: verifies:: [[openspec:lean-interop#ELPI data types#Higher-order data is rejected]]
/-- error: elpi_data: lam: a constructor argument of function type is higher-order; plain data only (use the LF extension for binders) -/
#guard_msgs in
elpi_data lp%{
  kind tm type.
  type lam (tm -> tm) -> tm.
}%

-- @tg: verifies:: [[openspec:lean-interop#ELPI data types#Unknown ELPI type is rejected]]
/-- error: elpi_data: rule.mk: the ELPI type prop has no Lean counterpart (declare it in the same block, or with `deriving Elpi`) -/
#guard_msgs in
elpi_data lp%{
  kind rule type.
  type rule.mk prop -> rule.
}%
