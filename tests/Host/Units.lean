import TestUtil
open Elpi TestUtil

/-- A generated signature of 200 lines. -/
def signature200 : String :=
  let kinds := (List.range 199).map fun i => s!"kind k{i} type."
  "\n".intercalate (kinds ++ ["kind person type."])

-- @tg: verifies:: [[openspec:elpi-host-api#Multi-unit load keeps positions#Error position inside the module]]
#eval show IO Unit from do
  check ((signature200.splitOn "\n").length == 200) "the signature has 200 lines"
  -- line 3, column 10 (columns count from 0, as in Lean positions): the 7 is not a person
  let rules := "pred ok i:person.\nok _.\nok _:- ok 7.\n"
  match Host.loadUnits [("signature", signature200), ("org-rules", rules)] with
  | .error (.located (d :: _)) =>
    expectEq d.unit "org-rules" "unit"
    expectEq d.line 3 "line"
    expectEq d.col 10 "column"
  | .error e => fail s!"expected a located error, got {e}"
  | .ok _ => fail "the module must be rejected"
  -- a parse error is located the same way
  match Host.loadUnits [("signature", signature200), ("org-rules", "pred ok o:int.\nok 1.\nok X :- ).\n")] with
  | .error (.located (d :: _)) => check (d.unit == "org-rules" && d.line == 3) s!"parse error at {d.unit}:{d.line}"
  | _ => fail "a parse error must be located"
  -- both units form one program
  match Host.loadUnits [("signature", signature200), ("org-rules", "pred ok o:person.\n")] with
  | .ok p => check (Host.predSig? p "ok").isSome "the module sees the signature's kinds"
  | .error e => fail s!"{e}"
