import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-cli#Interactive REPL#REPL answers queries against loaded files]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "p.elpi") "pred p o:int.\np 1.\np 2.\n"
    -- ask for a query, take both solutions, then an unsolvable query, then end the input
    let (code, out, _) ← runCli #[(dir / "p.elpi").toString] (stdin := "p X.\ny\nn\nfail.\n")
    expectEq code 0 "exit status at end of input"
    check (hasSub out "X = 1") s!"first solution missing: {out}"
    check (hasSub out "X = 2") s!"second solution missing: {out}"
    check (hasSub out "Failure") s!"failure must be reported: {out}"
