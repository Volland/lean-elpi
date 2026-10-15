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
  /-- Number of type parameters; the ELPI kind takes as many arguments. -/
  arity : Nat := 0
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

/-- The ELPI type variable for the `i`-th type parameter: `A`, `B`, … -/
def paramVarName (i : Nat) : String := String.singleton (Char.ofNat ('A'.toNat + i))

/-- Parenthesise a compound ELPI type when it is an argument of another type. -/
def parenTy (s : String) : String := if s.contains ' ' then s!"({s})" else s

/-- ELPI type of a Lean field type (bare: compound types are not parenthesised), or an error
naming the unsupported type. `params` maps the type parameters of the declaration being
derived to their ELPI type variables; `self` applied to exactly those parameters is the
declaration itself. -/
partial def elpiTypeOf (self : Name) (selfKind : String) (params : Array (FVarId × String))
    (derived : Array DeriveEntry) (ty : Expr) : Except String String := do
  if let some id := ty.fvarId? then
    match params.find? (·.1 == id) with
    | some (_, v) => return v
    | none => throw s!"no ToElpi instance for the field type {ty}"
  let sub := elpiTypeOf self selfKind params derived
  match ty.getAppFn.constName?, ty.getAppArgs.toList with
  | some n, [] =>
    if n == self && params.isEmpty then return selfKind
    else if n == ``Nat || n == ``Int then return "int"
    else if n == ``String then return "string"
    else if n == ``Bool then return "bool"
    else if n == ``Float then return "float"
    else if n == ``Name then return "name"
    else if n == ``Level then return "level"
    else if n == ``Expr then return "term"
    else
      match derived.find? fun e => e.leanName == n && e.arity == 0 with
      | some e => return e.kind
      | none => throw s!"no ToElpi instance for the field type {n}"
  | some n, args =>
    if n == self then
      let ok := args.length == params.size &&
        (args.zip params.toList).all fun (a, p) => a.fvarId? == some p.1
      unless ok do
        throw s!"{n} is applied to arguments other than its own parameters, which plain ELPI types cannot express"
      return " ".intercalate (selfKind :: params.toList.map (·.2))
    else match args with
    | [a] =>
      if n == ``List || n == ``Array then return s!"list {parenTy (← sub a)}"
      else if n == ``Option then return s!"option {parenTy (← sub a)}"
      else general n args
    | [a, b] =>
      if n == ``Prod then return s!"pair {parenTy (← sub a)} {parenTy (← sub b)}"
      else general n args
    | _ => general n args
  | _, _ => throw s!"no ToElpi instance for the field type {ty}"
where
  general (n : Name) (args : List Expr) : Except String String :=
    match derived.find? fun e => e.leanName == n && e.arity == args.length with
    | some e => do
      let tys ← args.mapM fun a => elpiTypeOf self selfKind params derived a
      return " ".intercalate (e.kind :: tys.map parenTy)
    | none => throw s!"no ToElpi instance for the field type {ty}"

/-- Constructor field types (explicit fields after the parameters), with the parameters as
free variables: `k` receives them with the field types. -/
def ctorFields {α : Type} (ctor : ConstructorVal)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  Meta.forallTelescope ctor.type fun xs _ => do
    let mut out := #[]
    for i in [ctor.numParams:xs.size] do
      out := out.push (← Meta.inferType xs[i]!)
    k (xs.extract 0 ctor.numParams) out

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

/-- Check that every type parameter of `ind` is a plain `Type`. -/
def checkParams (ind : InductiveVal) : MetaM Unit :=
  Meta.forallTelescope ind.type fun xs _ => do
    for i in [0:ind.numParams] do
      let ty ← Meta.whnf (← Meta.inferType xs[i]!)
      unless ty == mkSort Level.one do
        throwError "deriving Elpi: the parameter {i + 1} of {ind.name} is not a `Type`, which plain ELPI types cannot express"

-- @tg: implements:: [[openspec:lean-interop#Parametric and recursive deriving]]
def mkDeriveHandler (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let env ← getEnv
    let some (.inductInfo ind) := env.find? declName
      | throwError "deriving Elpi: {declName} is not an inductive type"
    unless ind.numIndices == 0 do
      throwError "deriving Elpi: {declName} is an indexed family, which plain ELPI types cannot express (use the LF extension)"
    liftTermElabM (checkParams ind)
    let kind := lowerFirst (shortName declName)
    let isStruct := isStructure env declName
    let derived := derivedEntries env
    let np := ind.numParams
    let pvars := (List.range np).map paramVarName
    let tn := declName.toString
    let root := "_root_." ++ tn
    -- ELPI declarations
    let kindDecl := s!"kind {kind} " ++ String.intercalate " -> " (List.replicate (np + 1) "type") ++ "."
    let resTy := " ".intercalate (kind :: pvars)
    let mut decls : List String := [kindDecl]
    let mut consts : List String := []
    let mut toArms : List String := []
    let mut constChecks : List String := []
    let mut appChecks : List String := []
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env.find? ctorName | throwError "deriving Elpi: missing constructor"
      let tys ← liftTermElabM <| ctorFields ctor fun ps fs => do
        let params := (ps.mapIdx fun i p => (p.fvarId!, paramVarName i))
        fs.toList.mapM fun t =>
          match elpiTypeOf declName kind params derived t with
          | .ok s => pure s
          | .error m => throwError "deriving Elpi: {m}"
      let eName := if isStruct then s!"{kind}.mk" else shortName ctorName
      let full := String.intercalate " -> " (tys ++ [resTy])
      decls := decls ++ [s!"type {eName} {full}."]
      if consts.contains eName then throwError "deriving Elpi: duplicate constructor name {eName}"
      consts := consts ++ [eName]
      let id := symbolId eName
      let n := tys.length
      let vars := (List.range n).map fun i => s!"a{i}"
      let pat := String.intercalate " " (s!"@_root_.{ctorName}" :: (List.replicate np "_") ++ vars)
      let toBody :=
        if n == 0 then s!"Elpi.Term.const ⟨{id}⟩"
        else s!"Elpi.Term.app (Elpi.Term.const ⟨{id}⟩) #[" ++ String.intercalate ", " (vars.map fun v => s!"Elpi.toElpi {v}") ++ "]"
      toArms := toArms ++ [s!"  | {pat} => {toBody}"]
      if n == 0 then
        constChecks := constChecks ++ [s!"if cid__.idx == {id} then .ok _root_.{ctorName} else"]
      else
        let binds := String.intercalate "\n        " ((List.range n).map fun i => s!"let a{i} ← Elpi.fromElpi args[{i}]!")
        appChecks := appChecks ++ [s!"if cid__.idx == {id} && args.size == {n} then do\n        {binds}\n        pure (_root_.{ctorName} {String.intercalate " " vars})\n      else"]
    -- name clashes with existing ELPI constants
    let base ← match baseProgram with
      | .ok b => pure b
      | .error e => throwError "{e}"
    for c in consts do
      if base.sig.consts.contains c || (derived.any fun e => e.consts.contains c)
          || reservedNames.contains c then
        throwError "deriving Elpi: the ELPI constant {c} already exists"
    -- the instances
    let ps := (List.range np).map fun i => s!"p{i}"
    let appTy := if np == 0 then root else s!"({root} " ++ " ".intercalate ps ++ ")"
    let binders (cls : String) := " ".intercalate (ps.map (s!"\{{·} : Type}"))
      ++ (if np == 0 then "" else " ") ++ " ".intercalate (ps.map fun p => s!"[Elpi.{cls} {p}]")
    let err := s!".error (Elpi.DecodeError.mk' \"{kind}\" t)"
    let ctorsFrom :=
      s!"  | Elpi.Term.const cid__ =>\n    {String.intercalate "\n    " constChecks} {err}\n" ++
      s!"  | Elpi.Term.app (Elpi.Term.const cid__) args =>\n      {String.intercalate "\n      " appChecks} {err}"
    let text := s!"
partial def {tn}.toElpiImpl {binders "ToElpi"} : {appTy} → Elpi.Term := fun x__ =>
  let _ : Elpi.ToElpi {appTy} := ⟨{tn}.toElpiImpl⟩
  match x__ with
{String.intercalate "\n" toArms}

partial def {tn}.fromElpiImpl {binders "FromElpi"} (t : Elpi.Term) : Except Elpi.DecodeError {appTy} :=
  let _ : Elpi.FromElpi {appTy} := ⟨\"{tn}\", {tn}.fromElpiImpl⟩
  match t with
{ctorsFrom}
  | _ => .error (Elpi.DecodeError.mk' \"{kind}\" t)

instance {binders "ToElpi"} : Elpi.ToElpi {appTy} := ⟨{tn}.toElpiImpl⟩
instance {binders "FromElpi"} : Elpi.FromElpi {appTy} := ⟨\"{tn}\", {tn}.fromElpiImpl⟩
"
    elabText text
    modifyEnv fun env => deriveExt.addEntry env { kind, leanName := declName, decls, consts, arity := np }
  return true

-- @tg: implements:: [[openspec:lean-reflection#Deriving Elpi]]
initialize registerDerivingHandler ``_root_.Elpi mkDeriveHandler

end Elpi
