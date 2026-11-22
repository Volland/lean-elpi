import TestUtil
open Elpi TestUtil

def graphBase : String := "pred edge o:int.\nedge 1.\nedge 2.\n"

-- @tg: verifies:: [[openspec:elpi-host-api#Host libraries for accumulate#Stored module is accumulated]]
#eval show IO Unit from do
  let rules := "accumulate graph-base.\npred two o:int.\ntwo N :- edge N, N > 1.\n"
  match Host.loadUnits [("org-rules", rules)] [("graph-base", graphBase)] with
  | .error e => fail s!"the library must resolve: {e}"
  | .ok p =>
    check (Host.predSig? p "edge").isSome "the library's predicate is declared"
    match Host.ast [("org-rules", rules)] [("graph-base", graphBase)] (view := (· == "org-rules")) with
    | .error e => fail s!"{e}"
    | .ok a =>
      check (a.clauses.all (·.pred == "two")) "the view shows only org-rules"
      expectEq a.accumulates.toList ["graph-base"] "accumulates of the viewed unit"
    match Host.ast [("org-rules", rules)] [("graph-base", graphBase)] with
    | .error e => fail s!"{e}"
    | .ok a => check (a.clauses.any (·.pred == "edge")) "host libraries may be shown"

-- @tg: verifies:: [[openspec:elpi-host-api#Host libraries for accumulate#Missing library is named]]
#eval show IO Unit from do
  match Host.loadUnits [("org-rules", "pred x o:int.\naccumulate graph-base.\n")] with
  | .error (.located (d :: _)) =>
    expectEq d.unit "org-rules" "unit"
    expectEq d.line 2 "line"
    check ((d.msg.splitOn "graph-base").length > 1) s!"the message names the library: {d.msg}"
  | .error e => fail s!"expected a located error, got {e}"
  | .ok _ => fail "a missing library must fail"
  -- an error inside a library is located in the library
  match Host.loadUnits [("org-rules", "accumulate graph-base.\n")] [("graph-base", "pred edge o:int.\nedge \"x\".\n")] with
  | .error (.located (d :: _)) => expectEq d.unit "graph-base" "unit of the error"
  | _ => fail "an ill-typed library must fail"

-- @tg: verifies:: [[openspec:elpi-host-api#Host libraries for accumulate#Accumulated names without loading]]
#eval show IO Unit from do
  match Host.accumulates "m" "accumulate a.\npred x o:int.\naccumulate b.\n" with
  | .ok names => expectEq names ["a", "b"] "accumulated names"
  | .error e => fail s!"{e}"
