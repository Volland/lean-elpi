import Lean
import Elpi.Lean.Marshal
import Elpi.Lean.Commands
import Elpi.Solver.Registry

/-!
# Type interoperability

The two directions of the Lean/ELPI type bridge, on top of `deriving Elpi`:

* **Lean to ELPI**: `elpi_extern` exposes an ordinary Lean function as a typed ELPI predicate
  (its signature is computed from the Lean type, its arguments are decoded with `FromElpi` and
  its result is encoded with `ToElpi`), and `#elpi_signature` shows the ELPI declarations that
  a derived Lean type contributes.
* **ELPI to Lean**: `elpi_data` takes plain ELPI `kind`/`type` declarations and defines the
  matching Lean inductive types with `deriving Elpi`, so the two sides cannot drift apart.
-/

-- @lat: [[components#Type interoperability]]

namespace Elpi

/-! ### Typed externs -/

/-- How a Lean function of type `F` is applied to the arguments of an ELPI call: each argument
is decoded with `FromElpi`; the final result type `R` is determined by `F`. -/
class ElpiFn (F : Type) (R : outParam Type) where
  apply : F → Array Term → Nat → Except DecodeError R

instance {α β R : Type} [FromElpi α] [ElpiFn β R] : ElpiFn (α → β) R where
  apply f args i := do
    let a ← FromElpi.fromElpi args[i]!
    ElpiFn.apply (f a) args (i + 1)

instance (priority := low) {R : Type} : ElpiFn R R := ⟨fun r _ _ => pure r⟩

namespace Extern

private def single (t : Term) : LazyList (Array Term) :=
  .cons #[t] (Thunk.mk fun _ => .nil)

/-- A total Lean function: one solution. A decoding failure makes the predicate fail. -/
def total {F R : Type} [ElpiFn F R] [ToElpi R] (f : F) (args : Array Term) :
    LazyList (Array Term) :=
  match ElpiFn.apply f args 0 with
  | .ok r => single (toElpi r)
  | .error _ => .nil

/-- A partial Lean function: `none` is failure. -/
def partial_ {F β : Type} [ElpiFn F (Option β)] [ToElpi β] (f : F) (args : Array Term) :
    LazyList (Array Term) :=
  match ElpiFn.apply f args 0 with
  | .ok (some r) => single (toElpi r)
  | _ => .nil

/-- A multi-valued Lean function: each element of the list is one solution, in order. -/
def many {F β : Type} [ElpiFn F (List β)] [ToElpi β] (f : F) (args : Array Term) :
    LazyList (Array Term) :=
  match ElpiFn.apply f args 0 with
  | .ok rs => LazyList.ofList (rs.map fun r => #[toElpi r])
  | .error _ => .nil

end Extern

end Elpi

namespace Elpi.Cmd

open _root_.Lean Elab Command Meta

syntax (name := elpiExtern) "elpi_extern " (&"partial" <|> &"many")? ident (" as " str)? : command

/-- Argument types and result type of a function type; every binder must be explicit and
non-dependent. -/
private def splitFnType (ty : Expr) : MetaM (Array Expr × Expr) := do
  let mut args := #[]
  let mut cur ← whnf ty
  while cur.isForall do
    unless cur.bindingInfo!.isExplicit && !cur.bindingBody!.hasLooseBVars do
      throwError "elpi_extern: only functions with explicit, non-dependent arguments can be exposed"
    args := args.push cur.bindingDomain!
    cur := cur.bindingBody!
  return (args, cur)

-- @tg: implements:: [[openspec:lean-interop#Typed Lean externs]]
@[command_elab elpiExtern] def elabExtern : CommandElab := fun stx => do
  let mode := if stx[1].isNone then "total" else (stx[1].reprint.getD "").trimAscii.toString
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let info ← getConstInfo fn
  unless info.levelParams.isEmpty do
    throwErrorAt stx[2] "elpi_extern: {fn} is universe polymorphic"
  let elpiName :=
    if stx[3].isNone then lowerFirst fn.toString else (stx[3][1].isStrLit?).getD ""
  let derived := derivedEntries (← getEnv)
  let tyOf (t : Expr) : CommandElabM String :=
    match elpiTypeOf .anonymous "" #[] derived t with
    | .ok s => pure s
    | .error m => throwErrorAt stx[2] "elpi_extern: {m}"
  let (argTys, resTy) ← liftTermElabM (splitFnType info.type)
  let outTy ← match mode with
    | "total" => pure resTy
    | "partial" =>
      unless resTy.isAppOfArity ``Option 1 do
        throwErrorAt stx[2] "elpi_extern partial: the result type must be `Option _`"
      pure resTy.appArg!
    | _ =>
      unless resTy.isAppOfArity ``List 1 do
        throwErrorAt stx[2] "elpi_extern many: the result type must be `List _`"
      pure resTy.appArg!
  let ins ← argTys.toList.mapM fun t => do pure s!"i:{parenTy (← tyOf t)}"
  let out := s!"o:{parenTy (← tyOf outTy)}"
  let sigSrc := s!"pred {elpiName} " ++ ", ".intercalate (ins ++ [out]) ++ "."
  match Registry.checkSig elpiName sigSrc (derivedSignatures (← getEnv)) with
  | .error m => throwErrorAt stx[2] "elpi_extern: {m}"
  | .ok _ => pure ()
  if (Registry.entries (← getEnv)).any (·.name == elpiName) then
    throwErrorAt stx[2] "elpi_extern: a builtin named '{elpiName}' is already registered"
  let helper := match mode with
    | "total" => "Elpi.Extern.total"
    | "partial" => "Elpi.Extern.partial_"
    | _ => "Elpi.Extern.many"
  let wrapper := fn ++ `elpiExtern
  elabText s!"def {wrapper} : Array Elpi.Term → Elpi.LazyList (Array Elpi.Term) := {helper} @{fn}"
  modifyEnv fun env =>
    Registry.builtinExt.addEntry env { name := elpiName, sigSrc, declName := wrapper, effect := .pureFn }

/-! ### `#elpi_signature` -/

syntax (name := elpiSignature) "#elpi_signature " ident : command

-- @tg: implements:: [[openspec:lean-interop#Signature inspection]]
@[command_elab elpiSignature] def elabSignature : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  match (derivedEntries (← getEnv)).find? (·.leanName == n) with
  | some e => logInfoAt stx ("\n".intercalate e.decls)
  | none => throwErrorAt stx[1] "{n} has no ELPI declarations (add `deriving Elpi`)"

/-! ### `elpi_data` -/

syntax (name := elpiData) "elpi_data " lpBlock : command

/-- A constructor read from an ELPI `type` declaration. -/
private structure DataCtor where
  name : String
  fields : List STy
  deriving Inhabited

/-- Flatten `a -> b -> r` into its argument types and result type. -/
private partial def arrows : STy → List STy × STy
  | .arrow a b _ => let (xs, r) := arrows b; (a :: xs, r)
  | t => ([], t)

private def capitalize (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- Lean source for an ELPI field type, or an error naming what plain data cannot hold. -/
private partial def leanTy (kinds : List (String × String)) (vars : List String) :
    STy → Except String String
  | .arrow .. =>
    throw "a constructor argument of function type is higher-order; plain data only (use the LF extension for binders)"
  | .var v _ =>
    if vars.contains v then pure v
    else throw s!"the type variable {v} is not a parameter of the result type"
  | .con n args _ => do
    let args' ← args.mapM (leanTy kinds vars)
    let app (h : String) : String :=
      if args'.isEmpty then h else "(" ++ " ".intercalate (h :: args') ++ ")"
    match n, args'.length with
    | "int", 0 => pure "Int"
    | "string", 0 => pure "String"
    | "bool", 0 => pure "Bool"
    | "float", 0 => pure "Float"
    | "term", 0 => pure "Lean.Expr"
    | "name", 0 => pure "Lean.Name"
    | "level", 0 => pure "Lean.Level"
    | "list", 1 => pure (app "List")
    | "option", 1 => pure (app "Option")
    | "pair", 2 => pure s!"({args'[0]!} × {args'[1]!})"
    | _, _ =>
      match kinds.lookup n with
      | some l => pure (app l)
      | none => throw s!"the ELPI type {n} has no Lean counterpart (declare it in the same block, or with `deriving Elpi`)"

-- @tg: implements:: [[openspec:lean-interop#ELPI data types]]
@[command_elab elpiData] def elabData : CommandElab := fun stx => do
  let (text, _) := lpText stx[1]
  let ds ← match Parser.parseProgram "elpi_data" text with
    | .ok ds => pure ds
    | .error e => throwErrorAt stx[1] "{e.toString}"
  -- kinds (name, arity) in order, then constructors
  let mut kinds : Array (String × Nat) := #[]
  let mut ctors : Array (String × DataCtor × List String) := #[]
  for d in ds do
    match d with
    | .kind names ty _ =>
      let (xs, r) := arrows ty
      unless (match r with | .con "type" [] _ => xs.all (fun | .con "type" [] _ => true | _ => false) | _ => false) do
        throwErrorAt stx[1] "elpi_data: the kind of {names} must be `type -> … -> type`"
      for n in names do kinds := kinds.push (n, xs.length)
    | .type names ty _ =>
      let (fields, res) := arrows ty
      let (rk, rargs) ← match res with
        | .con k args _ => pure (k, args)
        | _ => throwErrorAt stx[1] "elpi_data: the result type of {names} is not a data type"
      let pvars ← rargs.mapM fun
        | .var v _ => pure v
        | _ => throwErrorAt stx[1] "elpi_data: the result type of {names} must be applied to distinct type variables"
      if pvars.eraseDups.length != pvars.length then
        throwErrorAt stx[1] "elpi_data: the result type of {names} repeats a type variable"
      for n in names do
        if (n.splitOn ".").length > 1 && n != s!"{rk}.mk" then
          throwErrorAt stx[1] "elpi_data: constructor names must be simple (only `{rk}.mk` may be dotted, and it makes a structure): {n}"
        ctors := ctors.push (rk, { name := n, fields }, pvars)
    | _ => throwErrorAt stx[1] "elpi_data accepts only `kind` and `type` declarations"
  let leanKinds := (kinds.toList.map fun (k, _) => (k, capitalize k))
  for (k, ar) in kinds do
    if (k.splitOn ".").length > 1 then
      throwErrorAt stx[1] "elpi_data: kind names must be simple: {k}"
    if k == capitalize k then
      throwErrorAt stx[1] "elpi_data: the kind {k} must start with a lower-case letter"
    let cs := ctors.toList.filter (·.1 == k)
    if cs.isEmpty then
      throwErrorAt stx[1] "elpi_data: the kind {k} has no constructors in this block"
    let some (_, _, pvars) := cs.head? | continue
    unless pvars.length == ar do
      throwErrorAt stx[1] "elpi_data: {k} takes {ar} arguments but its constructors use {pvars.length}"
    let mut arms : List String := []
    let isStruct := cs.length == 1 && cs.head!.2.1.name == s!"{k}.mk"
    for (_, c, pv) in cs do
      unless pv == pvars do
        throwErrorAt stx[1] "elpi_data: the constructors of {k} use different type variables"
      let tys ← c.fields.mapM fun f => match leanTy leanKinds pvars f with
        | .ok s => pure s
        | .error m => throwErrorAt stx[1] "elpi_data: {c.name}: {m}"
      if isStruct then
        let fs := (tys.zipIdx).map fun (t, i) => s!"(f{i} : {t})"
        arms := ["  mk :: " ++ " ".intercalate fs]
      else
        arms := arms ++ [s!"  | {c.name} : " ++ " → ".intercalate (tys ++ [" ".intercalate (capitalize k :: pvars)])]
    let binders := " ".intercalate (pvars.map fun v => s!"({v} : Type)")
    let kw := if isStruct then "structure" else "inductive"
    elabText s!"{kw} {capitalize k} {binders} where\n{"\n".intercalate arms}\n  deriving Elpi"

end Elpi.Cmd
