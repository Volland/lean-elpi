import Lean
import Elpi.LF.Erase
import Elpi.Lean.Libraries
import Elpi.Lean.Builtins
import Elpi.Solver.Registry

/-!
# CLI

The `lean-elpi` executable: upstream-compatible flags (`-exec`, `-test`, `-I`),
`--lean-env`, `--fuel` and a REPL.
-/

-- @lat: [[components#CLI]]

namespace Elpi.Cli

structure Opts where
  files : List String := []
  test : Bool := false
  exec : Option String := none
  includes : List String := []
  leanEnv : List String := []
  fuel : Nat := defaultFuel
  /-- `--lf-erase`: print the erasure of the `#lf` files and stop. -/
  lfErase : Bool := false
  /-- `--lf-proof QUERY`: answer an LF query on the `#lf` file, with proof terms. -/
  lfProof : Option String := none
  rest : List String := []

/-- Parse `FILE… [-test] [-exec P] [-I DIR] [--lean-env M1,M2] [--fuel N] [-- ARGS]`. -/
-- @tg: implements:: [[openspec:elpi-cli#Upstream-compatible command line]]
partial def parseArgs (args : List String) (o : Opts := {}) : Except String Opts :=
  match args with
  | [] => .ok { o with files := o.files.reverse, includes := o.includes.reverse }
  | "--" :: rest => .ok { o with files := o.files.reverse, includes := o.includes.reverse, rest }
  | "-test" :: r => parseArgs r { o with test := true }
  | "-exec" :: p :: r => parseArgs r { o with exec := some p }
  | "-exec" :: [] => .error "-exec expects a predicate name"
  | "-I" :: d :: r => parseArgs r { o with includes := d :: o.includes }
  | "-I" :: [] => .error "-I expects a directory"
  | "--lean-env" :: ms :: r =>
    parseArgs r { o with leanEnv := (ms.splitOn ",").filter (· != "") }
  | "--lean-env" :: [] => .error "--lean-env expects a module list"
  | "--lf-erase" :: r => parseArgs r { o with lfErase := true }
  | "--lf-proof" :: q :: r => parseArgs r { o with lfProof := some q }
  | "--lf-proof" :: [] => .error "--lf-proof expects a query"
  | "--fuel" :: n :: r =>
    match n.toNat? with
    | some k => parseArgs r { o with fuel := k }
    | none => .error s!"--fuel expects a number, got '{n}'"
  | "--fuel" :: [] => .error "--fuel expects a number"
  | f :: r =>
    if f.startsWith "-" && f.length > 1 then .error s!"unknown option '{f}'"
    else parseArgs r { o with files := f :: o.files }

/-- Include paths for the library resolver. -/
-- @tg: implements:: [[openspec:elpi-cli#Include paths]]
def resolveIncludes (o : Opts) : Libraries.Config :=
  { includes := o.includes.map System.FilePath.mk }

/-- Hint appended to undeclared-constant errors when no Lean environment was loaded. -/
def envHint (msg : String) : String :=
  if (msg.splitOn "undeclared constant").length > 1 then
    msg ++ "\nhint: if this is a builtin registered by a Lean module, run with --lean-env MODULE"
  else msg

/-- Like `runOnce`, with the Lean-environment hint on undeclared constants. -/
def runOnceHint (p : CompiledProgram) (q : String) (fuel : Nat) : IO UInt32 := do
  try
    let st ← solveIO p q fuel
    match ← st.next with
    | some sol => reportConstraints sol; return 0
    | none => IO.eprintln "Failure"; return 1
  catch e =>
    IO.eprintln (envHint (toString e))
    return 1

/-- Run the first solution of a query in `MetaM` over the loaded Lean environment. -/
def runInMeta (env : _root_.Lean.Environment) (p : CompiledProgram) (q : String) (fuel : Nat) :
    IO UInt32 := do
  let bs ← match Registry.metaBuiltins env with
    | .ok bs => pure bs
    | .error e => IO.eprintln s!"lean-elpi: {e}"; return 1
  let act : _root_.Lean.Meta.MetaM (Except ElpiError (List Solution)) :=
    runIn (m := _root_.Lean.Meta.MetaM) p q bs (limit := 1) (fuel := fuel)
  let ctx : _root_.Lean.Core.Context := { fileName := "<lean-elpi>", fileMap := default }
  let st : _root_.Lean.Core.State := { env }
  let (r, _) ← (act.run' {} {}).toIO ctx st
  match r with
  | .ok (sol :: _) => reportConstraints sol; return 0
  | .ok [] => IO.eprintln "Failure"; return 1
  | .error e => IO.eprintln s!"{e}"; return 1

/-- Import the given Lean modules so that builtins registered there become available. -/
-- @tg: implements:: [[openspec:elpi-cli#Lean environment loading]]
unsafe def loadLeanEnv (mods : List String) : IO _root_.Lean.Environment := do
  _root_.Lean.initSearchPath (← _root_.Lean.findSysroot)
  _root_.Lean.enableInitializersExecution
  let imports := mods.toArray.map fun m => ({ module := m.toName } : _root_.Lean.Import)
  _root_.Lean.importModules imports {} (loadExts := true)

/-- Interactive loop: read queries ending in `.`, print bindings, offer further solutions. -/
-- @tg: implements:: [[openspec:elpi-cli#Interactive REPL]]
partial def repl (p : CompiledProgram) (fuel : Nat) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec readQuery (acc : String) : IO (Option String) := do
    let line ← stdin.getLine
    if line.isEmpty then return (if acc.trimAscii.isEmpty then none else some acc)
    let acc := acc ++ line
    if acc.trimAscii.toString.endsWith "." then return some acc else readQuery acc
  let rec loop : IO UInt32 := do
    stdout.putStr "?- "
    stdout.flush
    match ← readQuery "" with
    | none => return 0
    | some q =>
      let q := q.trimAscii.toString
      let q := (q.dropEnd 1).toString
      try
        let st ← solveIO p q fuel
        let mut n := 0
        repeat
          match ← st.next with
          | none =>
            if n == 0 then IO.println "Failure" else IO.println "No more solutions"
            break
          | some sol =>
            n := n + 1
            IO.println "Success:"
            for (v, t) in sol.bindings do
              IO.println s!"  {v} = {sol.show t}"
            for l in sol.constraintLines do IO.println l
            stdout.putStr "More? (y/N) "
            stdout.flush
            let ans ← stdin.getLine
            let a := ans.trimAscii.toString
            if !(a == "y" || a == ";") then break
      catch e => IO.eprintln s!"error: {e}"
      loop
  loop

end Elpi.Cli

open Elpi Elpi.Cli in
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"lean-elpi: {e}"
    return 2
  | .ok o =>
    let cfg := resolveIncludes o
    let env? ← if o.leanEnv.isEmpty then pure none else
      try pure (some (← unsafe loadLeanEnv o.leanEnv))
      catch e => IO.eprintln s!"lean-elpi: cannot load the Lean environment: {e}"; return 1
    let sigs := match env? with | some env => Registry.signatures env | none => []
    if o.lfErase || o.lfProof.isSome then
      let mut code : UInt32 := 0
      for f in o.files do
        let src ← IO.FS.readFile f
        let name := (f.splitOn "/").getLast!.replace ".elpi" ""
        match Elpi.LF.loadSource name f src with
        | .error e => IO.eprintln (toString e); code := 1
        | .ok sig =>
          if o.lfErase then IO.print (Elpi.LF.erase sig)
          if let some q := o.lfProof then
            match Elpi.LF.elaborate sig with
            | .error m => IO.eprintln m; code := 1
            | .ok lp =>
              let mut any := false
              for r in (Elpi.LF.runQuery sig lp q o.fuel).take 100 do
                match r with
                | .error e => IO.eprintln s!"error: {e}"; code := 1
                | .ok a =>
                  any := true
                  let b := a.showBindings
                  if !b.isEmpty then IO.println b
                  IO.println s!"proof: {a.showProof}"
              unless any do IO.println "Failure"
      (← IO.getStdout).flush
      return code
    let mut prog : Option CompiledProgram := none
    for f in o.files do
      let p ← match prog with
        | some p => pure p
        | none =>
          match Program.loadWith sigs "" with
          | .ok p => pure p
          | .error e => IO.eprintln (envHint (toString e)); return 1
      let find (name from_ : String) : IO (Option (String × String)) := do
        match ← Libraries.resolve cfg name from_ with
        | .ok r => return some r
        | .error _ => return none
      match ← loadUnits find f (← IO.FS.readFile f) (pre := Elpi.LF.preprocessUnit) with
      | .error e => IO.eprintln s!"{e.toString}"; return 1
      | .ok ds =>
        match p.addDecls ds with
        | .ok p' => prog := some p'
        | .error e => IO.eprintln (envHint (toString e)); return 1
    let p ← match prog with
      | some p => pure p
      | none =>
        match Program.loadWith sigs "" with
        | .ok p => pure p
        | .error e => IO.eprintln s!"{e}"; return 1
    -- constants nobody declared (untyped programs): reported, as the oracle does
    for w in p.warnings do
      IO.eprintln (envHint s!"warning: {w}")
    let query? : Option String :=
      if let some pred := o.exec then
        some s!"{pred} [{", ".intercalate (o.rest.map quoteArg)}]"
      else if o.test then some "main" else none
    let code ← match env?, query? with
      | some env, some q => runInMeta env p q o.fuel
      | _, some q =>
        runOnceHint p q o.fuel
      | _, none => repl p o.fuel
    (← IO.getStdout).flush
    return code
