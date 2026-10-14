import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-constraints#Residual constraints#Unsolved constraints are reported with the answer]]
#eval show IO Unit from do
  let p ← load "pred even i:int.\neven N :- 0 is N mod 2."
  match (solve p "declare_constraint (even X) [X], Y = 2").toList with
  | [.ok s] =>
    expectEq s.constraints.length 1 "exactly one residual constraint"
    match s.bindings.lookup "Y" with
    | some (.lit (.int 2)) => pure ()
    | _ => fail "Y must be 2"
    expectEq s.constraintLines [" even X0  /* suspended on X0 */"] "residual line"
  | _ => fail "expected exactly one solution"
  -- the CLI prints the answer and then the constraint
  withTmp fun dir => do
    IO.FS.writeFile (dir / "e.elpi") "pred even i:int.\neven N :- 0 is N mod 2.\n"
    let (code, out, _) ← runCli #[(dir / "e.elpi").toString]
      (stdin := "declare_constraint (even X) [X], Y = 2.\nn\n")
    expectEq code 0 "exit status"
    check (hasSub out "Y = 2") s!"answer missing: {out}"
    check (hasSub out "even X0  /* suspended on X0 */") s!"residual constraint missing: {out}"
