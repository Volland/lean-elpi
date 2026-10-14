import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-libraries#Embedded libraries#Binary resolves std without files on disk]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "prog.elpi") "main :- std.length [a, b] N, print N.\n"
    -- run from an empty directory: no lib/elpi/ exists next to the binary or the program
    let empty := dir / "empty"
    IO.FS.createDirAll empty
    let (code, out, err) ← runCli #["-test", (dir / "prog.elpi").toString] (cwd := some empty)
    expectEq code 0 s!"exit status ({err})"
    expectEq out "2\n" "standard output"
