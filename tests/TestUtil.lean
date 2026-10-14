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

end TestUtil
