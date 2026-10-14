import Lean
import Elpi.Runtime.Api

/-!
# Solver registry

Tier T2 of the solver API: Lean functions declared as ELPI predicates with
`@[elpi_builtin "name" "pred name m1:T1, …."]`. Signatures are parsed and typechecked when
the attribute is applied; entries live in a persistent environment extension so every
importing module sees them.
-/

-- @lat: [[components#Solver registry]]

namespace Elpi.Registry

open _root_.Lean

/-- What a registered implementation may do, inferred from its Lean type. -/
inductive Effect where
  | pureFn | ioFn | metaFn
  deriving Inhabited, BEq, Repr

structure Entry where
  name : String
  sigSrc : String
  declName : Name
  effect : Effect
  deriving Inhabited

initialize builtinExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := fun es e => es.push e
      addImportedFn := fun as => as.foldl (init := #[]) fun acc a => acc ++ a }

/-- Builtins visible in an environment (declared in it or in its imports). -/
def entries (env : Environment) : Array Entry := builtinExt.getState env

/-- Effect of an implementation from its type: `Array Term → LazyList …`, `… → IO (…)` or
`… → MetaM (…)`. -/
def effectOfType (ty : Expr) : Option Effect :=
  match ty.getForallBody.getAppFn.constName? with
  | some n =>
    if n == ``Elpi.LazyList then some .pureFn
    else if n == `IO then some .ioFn
    else if n == ``Lean.Meta.MetaM then some .metaFn
    else none
  | none => none

/-- Parse and typecheck a builtin signature string; the result is the `pred` declaration. -/
def checkSig (name sigSrc : String) : Except String Decl := do
  let ds ← match Parser.parseProgram "<elpi_builtin>" sigSrc with
    | .ok ds => pure ds
    | .error e => throw s!"invalid builtin signature: {e.toString}"
  match ds with
  | [d@(.pred n _ _)] =>
    if n != name then throw s!"signature declares '{n}' but the builtin is named '{name}'"
    let base ← match baseProgram with
      | .ok b => pure b
      | .error e => throw (toString e)
    match Typecheck.checkSignature base.sig d with
    | .ok _ => pure d
    | .error e => throw s!"invalid builtin signature: {e.toString}"
  | _ => throw "a builtin signature must be a single 'pred' declaration"

syntax (name := elpi_builtin) "elpi_builtin " str ppSpace str : attr

-- @tg: implements:: [[openspec:elpi-solver-api#Attribute registration]]
initialize elpiBuiltinAttr : Unit ←
  registerBuiltinAttribute
    { ref := by exact decl_name%
      name := `elpi_builtin
      descr := "Lean implementation of an ELPI builtin predicate"
      applicationTime := .afterCompilation
      add := fun declName stx _ => do
        let some name := stx[1].isStrLit? | throwError "elpi_builtin: name must be a string literal"
        let some sigSrc := stx[2].isStrLit? | throwError "elpi_builtin: signature must be a string literal"
        match checkSig name sigSrc with
        | .error msg => throwError msg
        | .ok _ => pure ()
        let env ← getEnv
        if (entries env).any (·.name == name) then
          throwError "elpi_builtin: a builtin named '{name}' is already registered"
        let info ← getConstInfo declName
        let some effect := effectOfType info.type
          | throwError "elpi_builtin: {declName} must have type `Array Term → LazyList (Array Term)`, optionally in `IO` or `MetaM`"
        modifyEnv fun env => builtinExt.addEntry env { name, sigSrc, declName, effect } }

/-- Signature sources of the registered builtins, to be loaded with a program. -/
def signatures (env : Environment) : List String := (entries env).toList.map (·.sigSrc)

unsafe def evalImplUnsafe {α : Type} (env : Environment) (opts : Options) (n : Name) :
    Except String α := env.evalConst α opts n

@[implemented_by evalImplUnsafe]
opaque evalImpl {α : Type} (env : Environment) (opts : Options) (n : Name) : Except String α

/-- Modes of the output positions in the signature of `e`. -/
def modesOf (e : Entry) : Except String (Array Mode) := do
  match ← checkSig e.name e.sigSrc with
  | .pred _ args _ => pure (args.map (·.1)).toArray
  | _ => throw "bad signature"

/-- The pure implementations of the registered builtins, as `Builtin Id` values. -/
def pureBuiltins (env : Environment) (opts : Options := {}) : Except String (List (Builtin Id)) := do
  let mut out := []
  for e in entries env do
    if e.effect == .pureFn then
      let f : Array Term → LazyList (Array Term) ← evalImpl env opts e.declName
      let modes ← modesOf e
      out := Builtin.ofOutputs { name := e.name, modes, type := .con "any" [] }
        (fun ctx args => f (args.map (ctx.store.zonk · ctx.depth))) :: out
  return out

/-- Builtins usable in `IO` (pure and `IO` implementations). -/
def ioBuiltins (env : Environment) (opts : Options := {}) : Except String (List (Builtin IO)) := do
  let mut out := []
  for e in entries env do
    let modes ← modesOf e
    let sig : BuiltinSig := { name := e.name, modes, type := .con "any" [] }
    match e.effect with
    | .pureFn =>
      let f : Array Term → LazyList (Array Term) ← evalImpl env opts e.declName
      out := Builtin.ofOutputs sig (fun ctx args => pure (f (args.map (ctx.store.zonk · ctx.depth)))) :: out
    | .ioFn =>
      let f : Array Term → IO (LazyList (Array Term)) ← evalImpl env opts e.declName
      out := Builtin.ofOutputs sig (fun ctx args => f (args.map (ctx.store.zonk · ctx.depth))) :: out
    | .metaFn => pure ()
  return out

/-- Builtins usable in `MetaM` (all effects). -/
def metaBuiltins (env : Environment) (opts : Options := {}) :
    Except String (List (Builtin Meta.MetaM)) := do
  let mut out : List (Builtin Meta.MetaM) := []
  for e in entries env do
    let modes ← modesOf e
    let sig : BuiltinSig := { name := e.name, modes, type := .con "any" [] }
    match e.effect with
    | .pureFn =>
      let f : Array Term → LazyList (Array Term) ← evalImpl env opts e.declName
      out := Builtin.ofOutputs sig (fun ctx args => pure (f (args.map (ctx.store.zonk · ctx.depth)))) :: out
    | .ioFn =>
      let f : Array Term → IO (LazyList (Array Term)) ← evalImpl env opts e.declName
      out := Builtin.ofOutputs sig (fun ctx args => (monadLift (f (args.map (ctx.store.zonk · ctx.depth))) : Meta.MetaM _)) :: out
    | .metaFn =>
      let f : Array Term → Meta.MetaM (LazyList (Array Term)) ← evalImpl env opts e.declName
      out := Builtin.ofOutputs sig (fun ctx args => f (args.map (ctx.store.zonk · ctx.depth))) :: out
  return out

/-- Load a program in an environment: it sees exactly the builtins registered there. -/
def loadIn (env : Environment) (src : String) : Except ElpiError CompiledProgram := do
  let p ← Program.loadWith (signatures env) src
  let bs ← match pureBuiltins env with
    | .ok bs => pure bs
    | .error e => throw (.load e)
  return { p with extra := bs ++ p.extra }

end Elpi.Registry
