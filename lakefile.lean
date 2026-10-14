import Lake

open System Lake DSL

package «lean-elpi» where
  testDriver := "Tests"
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target] lean_lib Elpi where precompileModules := true

lean_lib Tests where
  srcDir := "tests"
  roots := #[`TestUtil]
  globs :=
  #[`TestUtil, `Solver.RegistrationA, `Core.+, `Constraints.+, `Typecheck.+, `Solver.+, `Runtime.+, `Libraries.+, `Cli.+, `LF.+, `LeanHost.Program.A, `LeanHost.+,
    `Conformance.Harness]
  needs := #[`@/«lean-elpi»]

@[default_target] lean_exe «lean-elpi» where
  root := `Elpi.Cli.Main
  supportInterpreter := true

/-- Differential conformance run against the ELPI 1.18 oracle (`lake build` first). -/
script conformance (args) do
  let child ← IO.Process.spawn { cmd := "bash", args := #["tests/conformance/run.sh"] ++ args.toArray }
  child.wait
