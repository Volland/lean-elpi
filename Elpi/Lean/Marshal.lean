import Lean
import Elpi.Runtime.Api
import Elpi.Lean.Reflect

/-!
# Marshalling

`ToElpi`/`FromElpi` instances for the Lean types (`Name`, `Level`, `Expr`) and the
`deriving Elpi` handler, which generates the instances of an inductive type or structure and
registers its ELPI declarations (`kind`/`type`) in an environment extension, so every program
loaded in that environment can use them.
-/

-- @lat: [[components#Marshalling]]

/-- Marker class so `deriving Elpi` has a class to name; the handler generates `ToElpi` and
`FromElpi` instances. -/
class Elpi (α : Type) : Type

namespace Elpi

open _root_.Lean Elab Command

/-! ### Instances for Lean data -/

instance : ToElpi Name := ⟨Reflect.nameTerm⟩
instance : FromElpi Name where
  tyName := "Name"
  fromElpi t :=
    match Reflect.opaqueOf "name" t with
    | .ok d => .ok (Reflect.nameDec d)
    | .error _ => .error (.mk' "name" t)

instance : ToElpi Level := ⟨Reflect.levelTerm⟩
instance : FromElpi Level where
  tyName := "Level"
  fromElpi t :=
    match Reflect.opaqueOf "level" t with
    | .ok d => match Reflect.levelDec d with
      | some l => .ok l
      | none => .error (.mk' "level" t)
    | .error _ => .error (.mk' "level" t)

instance : ToElpi Expr := ⟨fun e => (Reflect.toTerm e).toOption.getD (.const cFail)⟩
instance : FromElpi Expr where
  tyName := "Expr"
  fromElpi t :=
    match Reflect.ofTerm t with
    | .ok e => .ok e
    | .error _ => .error (.mk' "term" t)

/-! ### `deriving Elpi` -/

/-- ELPI declarations contributed by one derived type. -/
structure DeriveEntry where
  kind : String
  leanName : Name
  /-- `kind …` and `type …` declarations, one per element. -/
  decls : List String
  /-- ELPI constants introduced (kind constructors). -/
  consts : List String
  deriving Inhabited

initialize deriveExt : SimplePersistentEnvExtension DeriveEntry (Array DeriveEntry) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := fun es e => es.push e
      addImportedFn := fun as => as.foldl (init := #[]) fun acc a => acc ++ a }

def derivedEntries (env : Environment) : Array DeriveEntry := deriveExt.getState env

/-- All derived declarations of an environment, as program source for `Program.loadWith`. -/
def derivedSignatures (env : Environment) : List String :=
  (derivedEntries env).toList.flatMap (·.decls)

def lowerFirst (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toLower :: cs)

/-- Short name of a declaration: the last component. -/
def shortName (n : Name) : String := n.getString!

/-- ELPI type of a Lean field type, or an error naming the unsupported type. -/
partial def elpiTypeOf (self : Name) (selfKind : String) (derived : Array DeriveEntry)
    (ty : Expr) : Except String String := do
  match ty.getAppFn.constName?, ty.getAppArgs.toList with
  | some n, [] =>
    if n == self then return selfKind
    else if n == ``Nat || n == ``Int then return "int"
    else if n == ``String then return "string"
    else if n == ``Bool then return "bool"
    else if n == ``Float then return "float"
    else if n == ``Name then return "name"
    else if n == ``Level then return "level"
    else if n == ``Expr then return "term"
    else
      match derived.find? (·.leanName == n) with
      | some e => return e.kind
      | none => throw s!"no ToElpi instance for the field type {n}"
  | some n, [a] =>
    if n == ``List || n == ``Array then return s!"(list {← elpiTypeOf self selfKind derived a})"
    else if n == ``Option then return s!"(option {← elpiTypeOf self selfKind derived a})"
    else throw s!"no ToElpi instance for the field type {ty}"
  | some n, [a, b] =>
    if n == ``Prod then
      return s!"(pair {← elpiTypeOf self selfKind derived a} {← elpiTypeOf self selfKind derived b})"
    else throw s!"no ToElpi instance for the field type {ty}"
  | _, _ => throw s!"no ToElpi instance for the field type {ty}"

/-- Constructor field types (explicit fields after the parameters). -/
def ctorFields (ctor : ConstructorVal) : MetaM (Array Expr) :=
  Meta.forallTelescope ctor.type fun xs _ => do
    let mut out := #[]
    for i in [ctor.numParams:xs.size] do
      out := out.push (← Meta.inferType xs[i]!)
    return out

/-- Parse and elaborate generated Lean source. -/
def elabText (text : String) : CommandElabM Unit := do
  let env ← getEnv
  let fileName := "<deriving Elpi>"
  let ictx := Parser.mkInputContext text fileName
  let mut pstate : Parser.ModuleParserState := {}
  let mut msgs : MessageLog := {}
  repeat
    let (cmd, ps, ms) := Parser.parseCommand ictx { env, options := {} } pstate msgs
    pstate := ps
    msgs := ms
    if Parser.isTerminalCommand cmd then break
    elabCommand cmd
  if msgs.hasErrors then
    throwError "generated code failed to parse: {← msgs.toList.mapM (·.toString)}"

def mkDeriveHandler (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let env ← getEnv
    let some (.inductInfo ind) := env.find? declName
      | throwError "deriving Elpi: {declName} is not an inductive type"
    unless ind.numParams == 0 && ind.numIndices == 0 do
      throwError "deriving Elpi: {declName} has parameters or indices, which are not supported"
    let kind := lowerFirst (shortName declName)
    let isStruct := isStructure env declName
    let derived := derivedEntries env
    -- ELPI declarations
    let mut decls : List String := [s!"kind {kind} type."]
    let mut consts : List String := []
    let mut toArms : List String := []
    let mut constChecks : List String := []
    let mut appChecks : List String := []
    let tn := declName.toString
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env.find? ctorName | throwError "deriving Elpi: missing constructor"
      let fields ← liftTermElabM (ctorFields ctor)
      let eName := if isStruct then s!"{kind}.mk" else shortName ctorName
      let tys ← fields.toList.mapM fun t =>
        match elpiTypeOf declName kind derived t with
        | .ok s => pure s
        | .error m => throwError "deriving Elpi: {m}"
      let full := String.intercalate " -> " (tys ++ [kind])
      decls := decls ++ [s!"type {eName} {full}."]
      if consts.contains eName then throwError "deriving Elpi: duplicate constructor name {eName}"
      consts := consts ++ [eName]
      let id := symbolId eName
      let n := fields.size
      let vars := (List.range n).map fun i => s!"a{i}"
      let pat := String.intercalate " " ((s!"@{ctorName}") :: vars)
      let toBody :=
        if n == 0 then s!"Elpi.Term.const ⟨{id}⟩"
        else s!"Elpi.Term.app (Elpi.Term.const ⟨{id}⟩) #[" ++ String.intercalate ", " (vars.map fun v => s!"Elpi.toElpi {v}") ++ "]"
      toArms := toArms ++ [s!"  | {pat} => {toBody}"]
      if n == 0 then
        constChecks := constChecks ++ [s!"if cid__.idx == {id} then .ok {ctorName} else"]
      else
        let binds := String.intercalate "\n        " ((List.range n).map fun i => s!"let a{i} ← Elpi.fromElpi args[{i}]!")
        appChecks := appChecks ++ [s!"if cid__.idx == {id} && args.size == {n} then do\n        {binds}\n        pure ({ctorName} {String.intercalate " " vars})\n      else"]
    -- name clashes with existing ELPI constants
    let base ← match baseProgram with
      | .ok b => pure b
      | .error e => throwError "{e}"
    for c in consts do
      if base.sig.consts.contains c || (derived.any fun e => e.consts.contains c)
          || reservedNames.contains c then
        throwError "deriving Elpi: the ELPI constant {c} already exists"
    -- the instances
    let err := s!".error (Elpi.DecodeError.mk' \"{kind}\" t)"
    let ctorsFrom :=
      s!"  | Elpi.Term.const cid__ =>\n    {String.intercalate "\n    " constChecks} {err}\n" ++
      s!"  | Elpi.Term.app (Elpi.Term.const cid__) args =>\n      {String.intercalate "\n      " appChecks} {err}"
    let text := s!"
partial def {tn}.toElpiImpl
  : {tn} → Elpi.Term
{String.intercalate "\n" toArms}

partial def {tn}.fromElpiImpl (t : Elpi.Term) : Except Elpi.DecodeError {tn} :=
  match t with
{ctorsFrom}
  | _ => .error (Elpi.DecodeError.mk' \"{kind}\" t)

instance : Elpi.ToElpi {tn} := ⟨{tn}.toElpiImpl⟩
instance : Elpi.FromElpi {tn} := ⟨\"{tn}\", {tn}.fromElpiImpl⟩
"
    elabText text
    modifyEnv fun env => deriveExt.addEntry env { kind, leanName := declName, decls, consts }
  return true

-- @tg: implements:: [[openspec:lean-reflection#Deriving Elpi]]
initialize registerDerivingHandler ``_root_.Elpi mkDeriveHandler

end Elpi
