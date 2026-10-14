import Lean
import Elpi.LF.Total
import Elpi.Lean.Commands
import Elpi.Lean.Marshal

/-!
# Lean commands for the LF layer

`lf_signature`, `#lf_query`, `lf_export` and `lf_certify`. A signature is stored in an
environment extension as its source text and reloaded on demand, so it survives imports.
-/

-- @lat: [[components#LF Lean commands]]

open Lean Elab Command

namespace Elpi.LFCmd

open Elpi Elpi.LF Elpi.Cmd

/-- `(name, label, source)` of a loaded signature. -/
abbrev LFEntry := String × String × String

-- @tg: implements:: [[openspec:elpi-lf#LF opt-in per file]]
initialize lfExt : SimplePersistentEnvExtension LFEntry (Array LFEntry) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := fun es e => es.push e
      addImportedFn := fun as => as.foldl (init := #[]) fun acc a => acc ++ a }

def sigEntries (env : Environment) : Array LFEntry := lfExt.getState env

/-- Load a declared signature. -/
def getSig (env : Environment) (name : String) : Except String LFSig :=
  match (sigEntries env).find? (·.1 == name) with
  | none => .error s!"unknown LF signature {name}; declare it with lf_signature"
  | some (_, label, src) =>
    match loadSource name label src with
    | .ok s => .ok s
    | .error e => .error (toString e)

syntax (name := lfSigFile) "lf_signature " ident str : command
syntax (name := lfSigInline) "lf_signature " ident lpBlock : command
syntax (name := lfQuery) "#lf_query " ident lpBlock : command
syntax (name := lfExport) "lf_export " ident : command
syntax (name := lfCertify) "lf_certify " ident ident lpBlock : command

private def declare (stx : Syntax) (name label src : String) : CommandElabM Unit := do
  if (sigEntries (← getEnv)).any (·.1 == name) then
    throwErrorAt stx "the LF signature {name} is already declared"
  let sig ← match loadSource name label src with
    | .ok s => pure s
    | .error e => throwErrorAt stx "{e}"
  let merrs := checkModes sig
  unless merrs.isEmpty do
    throwErrorAt stx "{"\n".intercalate (merrs.toList.map (·.toString))}"
  modifyEnv (lfExt.addEntry · (name, label, src))

@[command_elab lfSigFile] def elabSigFile : CommandElab := fun stx => do
  let name := stx[1].getId.toString
  let path := stx[2].isStrLit?.getD ""
  let (label, text) ← match ← liftIO (Libraries.resolve {} path (← getFileName)) with
    | .ok (_, t) => pure (path, t)
    | .error m => throwErrorAt stx[2] "{m}"
  declare stx name label text

@[command_elab lfSigInline] def elabSigInline : CommandElab := fun stx => do
  let (text, _) := lpText stx[2]
  declare stx stx[1].getId.toString "lp%" text

private def sigOf (stx : Syntax) : CommandElabM LFSig := do
  match getSig (← getEnv) stx.getId.toString with
  | .ok s => pure s
  | .error m => throwErrorAt stx "{m}"

/-- Compile the bridged Lean functions of a signature to closures (`Nat`-valued functions of
up to three `Nat` arguments). -/
unsafe def bridgeFnsUnsafe (sig : LFSig) : CoreM (Std.HashMap String BridgeFn) := do
  let mut out : Std.HashMap String BridgeFn := {}
  for (n, b) in sig.bridges.toList do
    let some ty := sig.consts[n]? | continue
    let arity := (peelPi ty).1.size
    let c := b.leanName.toName
    let f : Array Nat → Nat ← match arity with
      | 0 => do let v ← evalConst Nat c; pure fun _ => v
      | 1 => do let g ← evalConst (Nat → Nat) c; pure fun a => g a[0]!
      | 2 => do let g ← evalConst (Nat → Nat → Nat) c; pure fun a => g a[0]! a[1]!
      | 3 => do let g ← evalConst (Nat → Nat → Nat → Nat) c; pure fun a => g a[0]! a[1]! a[2]!
      | _ => throwError "bridged function {n} has too many arguments"
    out := out.insert n { arity, fn := f }
  return out

@[implemented_by bridgeFnsUnsafe]
opaque bridgeFns (sig : LFSig) : CoreM (Std.HashMap String BridgeFn)

private def programOf (stx : Syntax) (sig : LFSig) : CommandElabM CompiledProgram := do
  let fns ← liftCoreM (bridgeFns sig)
  match elaborate sig fns with
  | .ok p => pure p
  | .error m => throwErrorAt stx "{m}"

-- @tg: implements:: [[openspec:elpi-lf#Proof term recording]]
@[command_elab lfQuery] def elabLFQuery : CommandElab := fun stx => do
  let sig ← sigOf stx[1]
  let prog ← programOf stx[1] sig
  let (text, _) := lpText stx[2]
  let n := elpi.solutions.get (← getOptions)
  let mut any := false
  for r in (runQuery sig prog text).take n do
    match r with
    | .error e => throwErrorAt stx[2] "{e}"
    | .ok a =>
      any := true
      let b := a.showBindings
      let res := (if b.isEmpty then "" else b ++ "\n") ++ s!"proof: {a.showProof}"
      let res := if a.constraints.isEmpty then res
        else res ++ s!"\n(residual constraints: {a.constraints.length}; not certifiable)"
      logInfoAt stx res
  unless any do throwErrorAt stx "query has no solution"

@[command_elab lfExport] def elabLFExport : CommandElab := fun stx => do
  let sig ← sigOf stx[1]
  match exportSource sig with
  | .error e => throwErrorAt stx "{e}"
  | .ok src =>
    Elpi.elabText src
    -- totality claims: diagnostics, plus a kernel-checked theorem when a proof can be built
    for td in sig.totals do
      match checkTotal sig td with
      | .failed m => logErrorAt stx s!"totality of {td.fam}: {m}"
      | .ok summary =>
        logInfoAt stx summary
        match totalTheorem sig td with
        | .ok thm => Elpi.elabText thm
        | .error m => logWarningAt stx s!"no proof of totality of {td.fam} was built: {m}"

/-- The Lean expression of a translated certificate part. -/
partial def _root_.Elpi.LF.LExp.toExpr : LExp → Except String Expr
  | .app c as => do
    let args ← as.mapM Elpi.LF.LExp.toExpr
    return mkAppN (mkConst c.toName) args
  | .nat n => .ok (mkRawNatLit n)
  | .loc n => .error s!"unresolved local {n}"

/-- Add a theorem to the environment through the kernel. -/
def addTheorem (name : Name) (type value : Expr) : CoreM Unit := do
  -- a rejected declaration must leave no trace in the environment
  let saved ← getEnv
  try addDecl (.thmDecl { name, levelParams := [], type, value })
  catch e => setEnv saved; throw e

-- @tg: implements:: [[openspec:elpi-lf#Kernel-checked certificates]]
/-- Certify `proof` as a theorem `name` stating `fam args`; `recheck` runs the LF re-check
before the kernel sees the term. -/
def certifyProof (sig : LFSig) (syms : Symbols) (name : Name) (fam : String) (args : Array Term)
    (proof : Term) (recheck : Bool := true) : CoreM Unit := do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "refusing to certify while kernel checking is disabled (debug.skipKernelTC)"
  let fns ← bridgeFns sig
  let byLean : Std.HashMap String (Nat × (Array Nat → Nat)) :=
    sig.bridges.fold (init := {}) fun m n b =>
      match fns[n]? with | some f => m.insert b.leanName (f.arity, f.fn) | none => m
  match certificate sig syms fam args proof recheck (LExp.normBridge byLean) with
  | .error e => throwError "{e.msg}"
  | .ok (stmt, pr) =>
    match stmt.toExpr, pr.toExpr with
    | .ok t, .ok v => addTheorem name t v
    | .error m, _ | _, .error m => throwError "{m}"

@[command_elab lfCertify] def elabLFCertify : CommandElab := fun stx => do
  let sig ← sigOf stx[1]
  let prog ← programOf stx[1] sig
  let (text, _) := lpText stx[3]
  let name := (← getCurrNamespace) ++ stx[2].getId
  match (runQuery sig prog text).take 1 with
  | [] => throwErrorAt stx "query has no solution"
  | [.error e] => throwErrorAt stx[3] "{e}"
  | [.ok a] =>
    unless a.constraints.isEmpty do
      throwErrorAt stx "the answer has residual constraints and is not certified"
    let .atom fam args := a.ty | throwErrorAt stx "not a judgment"
    let args := args.map fun t => a.store.zonk t 0
    liftCoreM (certifyProof sig a.syms name fam args a.proof)
  | _ => throwErrorAt stx "unexpected query result"

end Elpi.LFCmd
