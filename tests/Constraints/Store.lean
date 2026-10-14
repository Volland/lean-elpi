import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-constraints#Backtrackable constraint store#Backtracking removes constraints added later]]
#eval show IO Unit from do
  let p ← load "pred p i:int.\np _.\npred q i:int.\nq _."
  for r in (solve p "(declare_constraint (p X) [X], fail ; true)").toList do
    match r with
    | .ok s => expectEq s.constraints.length 0 "the failed branch's constraint is gone"
    | .error e => fail s!"{e}"
  -- waking it in a failed branch is undone: it is still suspended, X unassigned
  match (solve p "declare_constraint (q X) [X], (X = 1, fail ; true)").toList with
  | [.ok s] =>
    expectEq s.constraints.length 1 "q X is still suspended"
    match s.bindings.lookup "X" with
    | some (.uvar _ _) => pure ()
    | _ => fail "X must be unassigned"
  | _ => fail "expected exactly one solution"
