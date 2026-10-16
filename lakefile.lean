import Lake

open System Lake DSL

package «lean-elpi» where
  testDriver := "Tests"
  version := v!"0.3.3"
  description := "λProlog inside Lean 4: write tactics, commands and proof search as logic programs, share types with Lean both ways, and get kernel-checked proofs."
  keywords := #["lambda-prolog", "elpi", "logic-programming", "metaprogramming", "tactics"]
  homepage := "https://volland.github.io/lean-elpi/"
  license := "Apache-2.0"
  licenseFiles := #["LICENSE"]
  readmeFile := "README.md"
  versionTags := .startsWith "v"
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- The ELPI sources that `Elpi.Std` embeds with `include_str`. Lake does not see those files as
inputs of the module, so without this a change to `lib/elpi/*.elpi` leaves a stale library. -/
input_dir elpiLibrary where
  path := "lib/elpi"
  text := true

@[default_target] lean_lib Elpi where
  precompileModules := true
  needs := #[elpiLibrary]

lean_lib Tests where
  srcDir := "tests"
  roots := #[`TestUtil]
  globs :=
  #[`TestUtil, `Solver.RegistrationA, `Core.+, `Constraints.+, `Typecheck.+, `Solver.+, `Runtime.+, `Libraries.+, `Cli.+, `LF.+, `LeanHost.Program.A, `LeanHost.+, `Interop.+,
    `conformance.Harness]
  needs := #[`@/«lean-elpi»]

@[default_target] lean_exe «lean-elpi» where
  root := `Elpi.Cli.Main
  supportInterpreter := true

/-- The Lean side of the C ABI behind the Python and Rust bindings; `scripts/build-ffi.sh`
links it with `ffi/leanelpi.c` into one shared library. -/
lean_lib ElpiFfi where
  roots := #[`Elpi.Ffi]
  needs := #[`@/«lean-elpi»]

/-- Differential conformance run against the ELPI 1.18 oracle (`lake build` first). -/
script conformance (args) do
  let child ← IO.Process.spawn { cmd := "bash", args := #["tests/conformance/run.sh"] ++ args.toArray }
  child.wait
