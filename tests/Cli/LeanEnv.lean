import TestUtil
open Elpi TestUtil

def leanPath : IO String := do
  let sysroot ← Lean.findSysroot
  let build := (← IO.FS.realPath ".lake/build/lib/lean").toString
  return s!"{build}:{sysroot}/lib/lean"

-- @tg: verifies:: [[openspec:elpi-cli#Lean environment loading#Lean builtins without an environment fail clearly]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "d.elpi") "main :- double 21 X, print X.\n"
    let (code, _, err) ← runCli #["-test", (dir / "d.elpi").toString]
    check (code != 0) "the Lean-only builtin must not run without an environment"
    check (hasSub err "double") s!"the error must name the builtin: {err}"
    check (hasSub err "--lean-env") s!"the error must hint at --lean-env: {err}"

-- @tg: verifies:: [[openspec:elpi-cli#Lean environment loading#Lean builtins work with --lean-env]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "d.elpi") "main :- double 21 X, print X.\n"
    let (code, out, err) ← runCli #["-test", (dir / "d.elpi").toString, "--lean-env", "Solver.RegistrationA"]
      (env := #[("LEAN_PATH", some (← leanPath))])
    expectEq code 0 s!"exit status ({err})"
    expectEq out "42\n" "standard output"
