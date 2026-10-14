import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-solver-api#CHR solvers in ELPI#leq solver detects a cycle]]
#eval show IO Unit from do
  let p ← load "accumulate leq."
  match (solve p "leq A B, leq B C, leq C A").toList with
  | [.ok s] =>
    expectEq s.constraints.length 0 "no residual leq constraints"
    match s.bindings.lookup "A", s.bindings.lookup "B", s.bindings.lookup "C" with
    | some (.uvar a _), some (.uvar b _), some (.uvar c _) =>
      check (a == b && b == c) "A, B and C must be unified"
    | _, _, _ => fail "A, B and C must be unassigned variables"
  | _ => fail "expected exactly one solution"
  -- two solvers coexist: each sees only the predicates of its own header
  let q ← load "accumulate leq.\nconstraint pos {\n  rule \\ (pos X N) | (N > 0) <=> true.\n}\npred pos o:int, o:int.\npos X N :- declare_constraint (pos X N) [X]."
  match (solve q "leq A B, pos X 1, pos Y 0").toList with
  | [.ok s] => expectEq s.constraints.length 2 "leq A B and pos Y 0 remain"
  | _ => fail "expected exactly one solution"
