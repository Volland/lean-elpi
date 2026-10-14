import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-cli#Upstream-compatible command line#Exec runs a predicate with arguments]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "ex.elpi") "pred go i:list string.\ngo L :- print L.\n"
    let (code, out, err) ← runCli #["-exec", "go", (dir / "ex.elpi").toString, "--", "a", "b"]
    expectEq code 0 s!"exit status ({err})"
    expectEq out "[a, b]\n" "standard output"
    -- a failing predicate gives a non-zero status
    IO.FS.writeFile (dir / "fl.elpi") "pred go i:list string.\ngo _ :- fail.\n"
    let (code, _, _) ← runCli #["-exec", "go", (dir / "fl.elpi").toString, "--", "x"]
    check (code != 0) "failure must give a non-zero exit status"

-- @tg: verifies:: [[openspec:elpi-cli#Upstream-compatible command line#Test flag runs the main predicate]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "t.elpi") "main :- print \"hello\".\n"
    let (code, out, _) ← runCli #["-test", (dir / "t.elpi").toString]
    expectEq code 0 "exit status"
    expectEq out "hello\n" "standard output"
