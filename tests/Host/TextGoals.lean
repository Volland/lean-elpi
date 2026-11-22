import TestUtil
open Elpi TestUtil

private def prog : IO CompiledProgram :=
  match Host.loadUnits [("test", "pred edge o:int.\nedge 1.\nedge 2.\npred ok.\nok.\n")] with
  | .ok p => pure p
  | .error e => fail s!"{e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Goals parsed from text#Text goal with outputs]]
#eval show IO Unit from do
  let p ← prog
  match Host.parseGoal p "edge X, X > 1" with
  | .error e => fail s!"{e}"
  | .ok q =>
    expectEq (q.names.map (·.1)).toList ["X"] "outputs are the named variables"
    match Host.solveSliced q 100 with
    | .ok sols =>
      expectEq sols.size 1 "one solution"
      check (sols[0]!.toList.map (fun (n, t) => s!"{n}={t}") == ["X=2"]) "X is 2"
    | .error e => fail s!"{e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Goals parsed from text#Syntax error in a text goal]]
#eval show IO Unit from do
  let p ← prog
  match Host.parseGoal p "edge X,, ok" with
  | .error (.located (d :: _)) =>
    expectEq d.unit "<goal>" "unit"
    expectEq d.line 1 "line"
    expectEq d.col 7 "column of the second comma"
  | .error e => fail s!"expected a located error, got {e}"
  | .ok _ => fail "the goal must be rejected"
