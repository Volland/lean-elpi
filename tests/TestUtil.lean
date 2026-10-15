import Elpi

/-!
Helpers shared by the golden tests. A test is an `#eval` of an `IO Unit` action: a
failed check throws, which makes elaboration (and therefore `lake test`) fail.
-/

open Elpi

namespace TestUtil

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

def check (b : Bool) (msg : String) : IO Unit := unless b do fail msg

def expectEq {α : Type} [BEq α] [ToString α] (got want : α) (what : String) : IO Unit :=
  unless got == want do fail s!"{what}: expected {want}, got {got}"

def load (src : String) : IO CompiledProgram :=
  match Program.load src with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

/-- Loading must fail; returns the error message. -/
def loadErr (src : String) : IO String :=
  match Program.load src with
  | .ok _ => fail "expected the program to be rejected, but it loaded"
  | .error e => pure (toString e)

/-- All solutions (at most `n`) as strings like `X = 1, Y = a`; errors abort the test. -/
def sols (p : CompiledProgram) (q : String) (n : Nat := 100) : IO (List String) := do
  let mut out := []
  for r in (solve p q).take n do
    match r with
    | .ok s => out := out ++ [toString s]
    | .error e => fail s!"query '{q}' raised: {e}"
  return out

/-- The terminal error of a query, if any. -/
def queryError (p : CompiledProgram) (q : String) (fuel : Nat := defaultFuel) :
    IO (Option ElpiError) := do
  for r in (solve p q fuel).toList do
    match r with
    | .error e => return some e
    | .ok _ => pure ()
  return none

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

end TestUtil

namespace TestUtil

/-- Path of the built CLI (tests run from the package root). -/
def cliPath : String := ".lake/build/bin/lean-elpi"

/-- Run the CLI with arguments, returning `(exit code, stdout, stderr)`. -/
def runCli (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) (stdin : String := "") :
    IO (UInt32 × String × String) := do
  let exe ← IO.FS.realPath cliPath
  let child ← IO.Process.spawn
    { cmd := exe.toString, args, cwd, env, stdin := .piped, stdout := .piped, stderr := .piped }
  let (inp, child) ← child.takeStdin
  inp.putStr stdin
  inp.flush
  let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept out.get
  return (code, out, err)

/-- Run `act` with a fresh temporary directory. -/
def withTmp {α : Type} (act : System.FilePath → IO α) : IO α := do
  let base := (System.FilePath.mk "/tmp") / s!"lean-elpi-test-{← IO.monoNanosNow}"
  IO.FS.createDirAll base
  try act base finally IO.FS.removeDirAll base


unsafe def enableInitUnsafe : IO Unit := Lean.enableInitializersExecution

@[implemented_by enableInitUnsafe] opaque enableInit : IO Unit

/-- `Environment.freeRegions` is `unsafe` (the environment must not be used afterwards). -/
unsafe def freeEnvUnsafe (env : Lean.Environment) : IO Unit := env.freeRegions

@[implemented_by freeEnvUnsafe] opaque freeEnv (env : Lean.Environment) : IO Unit

/-- Elaborate Lean source text (with its `import` header) and return the messages with their
positions: `(severity, line, column, text)`. -/
def elabSource (src : String) (fileName : String := "<test>") :
    IO (List (Lean.MessageSeverity × Nat × Nat × String)) := do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInit
  let inputCtx := Lean.Parser.mkInputContext src fileName
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← Lean.Elab.processHeader header {} messages inputCtx
  let cmdState := Lean.Elab.Command.mkState env messages {}
  let s ← Lean.Elab.IO.processCommands inputCtx parserState cmdState
  let mut out := []
  for m in s.commandState.messages.toList do
    out := out ++ [(m.severity, m.pos.line, m.pos.column, ← m.data.toString)]
  -- Release the imported .olean regions: every call imports `Lean` and `Elpi` afresh, and without
  -- this each one keeps about 2 GB mapped for the life of the process (a test with a dozen
  -- calls then needs more memory than a hosted CI runner has).
  freeEnv s.commandState.env
  return out

end TestUtil
