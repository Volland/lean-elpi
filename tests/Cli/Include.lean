import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-cli#Include paths#Include path resolves accumulate]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.createDirAll (dir / "inc")
    IO.FS.writeFile (dir / "inc" / "mylib.elpi") "pred hi.\nhi :- print \"from lib\".\n"
    IO.FS.writeFile (dir / "m.elpi") "accumulate mylib.\nmain :- hi.\n"
    let (code, _, err) ← runCli #["-test", (dir / "m.elpi").toString]
    check (code != 0) "without -I the accumulate must not resolve"
    check (hasSub err "mylib") s!"the error must name the library: {err}"
    let (code, out, err) ← runCli #["-test", (dir / "m.elpi").toString, "-I", (dir / "inc").toString]
    expectEq code 0 s!"exit status ({err})"
    expectEq out "from lib\n" "standard output"
