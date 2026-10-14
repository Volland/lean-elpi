import Std.Data.HashMap
import Std.Data.HashSet
import Elpi.Core.Parser

/-!
# Type checker

Load-time static checker: `kind`, `type` and `pred` declarations, argument modes, prenex
polymorphism and type abbreviations. HM-style first-order unification on simple types;
errors carry the source position, the expected and the inferred type.
-/

-- @lat: [[components#Type checker]]

namespace Elpi

/-- Simple types. `gen i` is a quantified variable of a scheme, `mv i` a unification
variable of the checker. -/
inductive Ty where
  | con (n : String) (args : List Ty)
  | arrow (a b : Ty)
  | mv (i : Nat)
  | gen (i : Nat)
  deriving Inhabited, BEq

partial def Ty.toString : Ty → String
  | .con n [] => n
  | .con n as => "(" ++ n ++ " " ++ " ".intercalate (as.map Ty.toString) ++ ")"
  | .arrow a b =>
    let l := match a with | .arrow .. => "(" ++ a.toString ++ ")" | _ => a.toString
    l ++ " -> " ++ b.toString
  | .mv i => s!"?{i}"
  | .gen i => s!"'{i}"

instance : ToString Ty := ⟨Ty.toString⟩

def tyProp : Ty := .con "prop" []

structure Scheme where
  nvars : Nat
  ty : Ty
  deriving Inhabited

structure Abbrev where
  params : List String
  body : STy
  deriving Inhabited

/-- The program signature: declared kinds, constants, abbreviations and modes. -/
structure Signature where
  kinds : Std.HashMap String Nat := {}
  consts : Std.HashMap String Scheme := {}
  abbrevs : Std.HashMap String Abbrev := {}
  modes : Std.HashMap String (Array Mode) := {}
  deriving Inhabited

structure TypeError where
  pos : Pos
  msg : String
  deriving Inhabited

def TypeError.toString (e : TypeError) : String := s!"{e.pos.toString}: {e.msg}"

namespace Typecheck

partial def mentionsTy (name : String) : STy → Bool
  | .con n as _ => n == name || as.any (mentionsTy name)
  | .arrow a b _ => mentionsTy name a || mentionsTy name b
  | .var .. => false

/-- Convert a surface type to `Ty`, expanding abbreviations eagerly. Type variables of
the declaration become `gen i` (assigned in order of first occurrence through `vars`). -/
-- @tg: implements:: [[openspec:elpi-typechecker#Type abbreviations]]
partial def expandAbbrev (sig : Signature) (t : STy) (vars : Array String)
    (fuel : Nat := 64) : Except TypeError (Ty × Array String) := do
  match t with
  | .var n _ =>
    match vars.findIdx? (· == n) with
    | some i => return (.gen i, vars)
    | none => return (.gen vars.size, vars.push n)
  | .arrow a b _ =>
    let (a', vars) ← expandAbbrev sig a vars fuel
    let (b', vars) ← expandAbbrev sig b vars fuel
    return (.arrow a' b', vars)
  | .con n args p =>
    let mut vars := vars
    let mut args' : Array Ty := #[]
    for a in args do
      let (a', v) ← expandAbbrev sig a vars fuel
      vars := v; args' := args'.push a'
    match sig.abbrevs[n]? with
    | some ab =>
      if fuel == 0 then throw { pos := p, msg := s!"cyclic type abbreviation '{n}'" }
      if ab.params.length != args'.size then
        throw { pos := p, msg := s!"type abbreviation '{n}' expects {ab.params.length} arguments" }
      -- expand the body with parameters replaced by the (already converted) arguments
      let rec subst : STy → Except TypeError (Ty × Array String)
        | .var v q =>
          match ab.params.findIdx? (· == v) with
          | some i => pure (args'[i]!, vars)
          | none => throw { pos := q, msg := s!"unbound type variable '{v}' in abbreviation" }
        | .arrow a b q => do
          let (a', _) ← subst a
          let (b', _) ← subst b
          pure (.arrow a' b', vars)
        | .con m as q => do
          if sig.abbrevs.contains m then
            expandAbbrev sig (.con m (as.map fun x => x) q) vars (fuel - 1)
              |>.map fun (t, v) => (t, v)
          else
            let mut out : Array Ty := #[]
            for a in as do
              let (a', _) ← subst a
              out := out.push a'
            pure (.con m out.toList, vars)
      -- abbreviations bodies refer to their own parameters, not the caller's variables
      let (body, _) ← subst ab.body
      return (body, vars)
    | none =>
      match sig.kinds[n]? with
      | some ar =>
        if ar != args'.size && n != "variadic" then
          throw { pos := p, msg := s!"type constructor '{n}' expects {ar} arguments but is applied to {args'.size}" }
        return (.con n args'.toList, vars)
      | none => throw { pos := p, msg := s!"unknown type '{n}'" }

/-- Number of arrows in a kind declaration `type -> type -> type`. -/
partial def kindArity : STy → Nat
  | .arrow _ b _ => 1 + kindArity b
  | _ => 0

/-- Register one declaration in the signature. -/
-- @tg: implements:: [[openspec:elpi-typechecker#Signature declarations]]
def checkSignature (sig : Signature) : Decl → Except TypeError Signature
  | .kind names ty _ =>
    return names.foldl (fun s n => { s with kinds := s.kinds.insert n (kindArity ty) }) sig
  | .typeabbrev name params body p => do
    match sig.abbrevs[name]? with
    | some _ => throw { pos := p, msg := s!"type abbreviation '{name}' is already defined" }
    | none => pure ()
    -- cycles: the body may not mention the abbreviation itself
    if mentionsTy name body then throw { pos := p, msg := s!"cyclic type abbreviation '{name}'" }
    return { sig with abbrevs := sig.abbrevs.insert name { params, body } }
  | .type names ty _ => do
    let (t, vars) ← expandAbbrev sig ty #[]
    return names.foldl (fun s n =>
      { s with consts := s.consts.insert n { nvars := vars.size, ty := t } }) sig
  | .pred name args _ => do
    let mut vars : Array String := #[]
    let mut tys : Array Ty := #[]
    for (_, a) in args do
      let (t, v) ← expandAbbrev sig a vars
      vars := v; tys := tys.push t
    let ty := tys.foldr (fun a acc => .arrow a acc) tyProp
    return { sig with
      consts := sig.consts.insert name { nvars := vars.size, ty },
      modes := sig.modes.insert name (args.map (·.1)).toArray }
  | _ => return sig

/-! ### Inference -/

structure TC where
  subst : Array (Option Ty) := #[]
  errors : Array TypeError := #[]
  /-- Types of clause variables of the clause being checked. -/
  vars : Std.HashMap String Ty := {}
  /-- Types of untyped but defined constants. -/
  implicit : Std.HashMap String Ty := {}

abbrev TCM := StateM TC

def freshMeta : TCM Ty := modifyGet fun s => (.mv s.subst.size, { s with subst := s.subst.push none })

partial def resolve (t : Ty) : TCM Ty := do
  match t with
  | .mv i =>
    match (← get).subst[i]! with
    | some t' => resolve t'
    | none => return t
  | _ => return t

partial def zonkTy (t : Ty) : TCM Ty := do
  match ← resolve t with
  | .con n as => return .con n (← as.mapM zonkTy)
  | .arrow a b => return .arrow (← zonkTy a) (← zonkTy b)
  | t => return t

partial def occurs (i : Nat) (t : Ty) : TCM Bool := do
  match ← resolve t with
  | .mv j => return i == j
  | .con _ as => as.anyM (occurs i)
  | .arrow a b => return (← occurs i a) || (← occurs i b)
  | _ => return false

partial def unifyTy (a b : Ty) : TCM Bool := do
  let a ← resolve a
  let b ← resolve b
  match a, b with
  | .mv i, .mv j =>
    if i == j then return true
    modify fun s => { s with subst := s.subst.set! i (some b) }
    return true
  | .mv i, t | t, .mv i =>
    if ← occurs i t then return false
    modify fun s => { s with subst := s.subst.set! i (some t) }
    return true
  | .con "any" [], _ | _, .con "any" [] => return true
  | .con n as, .con m bs =>
    if n != m || as.length != bs.length then return false
    for (x, y) in as.zip bs do
      unless ← unifyTy x y do return false
    return true
  | .arrow a1 b1, .arrow a2 b2 => return (← unifyTy a1 a2) && (← unifyTy b1 b2)
  | .gen i, .gen j => return i == j
  | _, _ => return false

/-- Instantiate a scheme with fresh type variables, independently at every use. -/
-- @tg: implements:: [[openspec:elpi-typechecker#Prenex polymorphism]]
def instantiate (sc : Scheme) : TCM Ty := do
  let mut ms : Array Ty := #[]
  for _ in [0:sc.nvars] do ms := ms.push (← freshMeta)
  let rec go : Ty → Ty
    | .gen i => ms[i]!
    | .con n as => .con n (as.map go)
    | .arrow a b => .arrow (go a) (go b)
    | t => t
  return go sc.ty

structure Env where
  sig : Signature
  /-- Constants that have clauses, hence are implicitly declared. -/
  defined : Std.HashSet String
  bound : List (String × Ty) := []

def report (p : Pos) (msg : String) : TCM Unit :=
  modify fun s => { s with errors := s.errors.push { pos := p, msg } }

/-- Unify, reporting a mismatch against the expected type at `p`. -/
def expect (p : Pos) (what : String) (expected inferred : Ty) : TCM Unit := do
  unless ← unifyTy expected inferred do
    let e ← zonkTy expected
    let i ← zonkTy inferred
    report p s!"{what} has type {i} but is used with type {e}"

def isMeta (t : Ty) : TCM Bool := do
  match ← resolve t with
  | .mv _ => return true
  | .con "any" [] => return true
  | _ => return false

def splitArrows (t : Ty) (n : Nat) : TCM (List Ty × Ty) := do
  let mut args : Array Ty := #[]
  let mut cur := t
  for _ in [0:n] do
    match ← resolve cur with
    | .arrow a b => args := args.push a; cur := b
    | .mv _ =>
      let a ← freshMeta
      let b ← freshMeta
      let _ ← unifyTy cur (.arrow a b)
      args := args.push a; cur := b
    | _ => return (args.toList, cur)
  return (args.toList, cur)

mutual
/-- Check `t` against `expected`. -/
partial def check (env : Env) (t : STm) (expected : Ty) : TCM Unit := do
  match t with
  | .int _ p => expect p (toString "integer") expected (.con "int" [])
  | .float _ p => expect p "float" expected (.con "float" [])
  | .str s p => expect p s!"\"{s}\"" expected (.con "string" [])
  | .spill g _ => check env g expected
  | .var n p =>
    let known ← if n == "_" then pure none else do pure ((← get).vars[n]?)
    let ty ← match known with
      | some ty => pure ty
      | none =>
        let ty ← freshMeta
        if n != "_" then modify fun s => { s with vars := s.vars.insert n ty }
        pure ty
    expect p n expected ty
  | .lam x b p =>
    let a ← freshMeta
    let r ← freshMeta
    expect p "abstraction" expected (.arrow a r)
    check { env with bound := (x, a) :: env.bound } b r
  | .const n p =>
    match env.bound.lookup n with
    | some ty => expect p n expected ty
    | none => checkConst env n p expected
  | .app f args p =>
    match f with
    | .const n fp =>
      match env.bound.lookup n with
      | some ty => checkSpine env ty args p expected n
      | none =>
        let ty ← constType env n fp expected (some args.length)
        checkSpine env ty args p expected n
    | .var .. =>
      let ty ← inferHead env f
      checkSpine env ty args p expected "variable"
    | _ =>
      let ty ← freshMeta
      check env f ty
      checkSpine env ty args p expected "term"

partial def inferHead (env : Env) (f : STm) : TCM Ty := do
  let ty ← freshMeta
  check env f ty
  return ty

/-- Type of a global constant: declared scheme, implicit (defined) type, or a fresh
variable for a constant that nobody declared. -/
partial def constType (env : Env) (n : String) (p : Pos) (expected : Ty)
    (nargs : Option Nat) : TCM Ty := do
  match env.sig.consts[n]? with
  | some sc => instantiate sc
  | none =>
    match (← get).implicit[n]? with
    | some ty => return ty
    | none =>
      let ty ← freshMeta
      modify fun s => { s with implicit := s.implicit.insert n ty }
      -- an undeclared constant with no clauses used where the type is known is an error
      if !(env.defined.contains n) then
        let isHead := nargs.isSome
        let concrete := !(← isMeta expected)
        if concrete || isHead then
          if concrete then
            report p s!"undeclared constant '{n}'"
      return ty

partial def checkConst (env : Env) (n : String) (p : Pos) (expected : Ty) : TCM Unit := do
  let ty ← constType env n p expected none
  expect p n expected ty

partial def checkSpine (env : Env) (fty : Ty) (args : List STm) (p : Pos) (expected : Ty)
    (what : String) : TCM Unit := do
  -- variadic constants accept any number of arguments of one type
  match ← resolve fty with
  | .con "variadic" [a, r] =>
    for x in args do check env x a
    expect p what expected r
  | _ =>
    let (tys, res) ← splitArrows fty args.length
    if tys.length < args.length then
      report p s!"{what} is applied to {args.length} arguments but its type {← zonkTy fty} takes {tys.length}"
    else
      for (x, a) in args.zip tys do check env x a
      expect p s!"application of {what}" expected res
end

/-- Variables of the clause are local to it. -/
def checkClause (env : Env) (t : STm) : TCM Unit := do
  modify fun s => { s with vars := {} }
  check env t tyProp

/-- Name of the predicate a clause defines. -/
partial def clauseHead : STm → Option String
  | .app (.const ":-" _) [h, _] _ => clauseHead h
  | .app (.const "," _) (h :: _) _ => clauseHead h
  | .app (.const n _) _ _ => some n
  | .const n _ => some n
  | _ => none

/-- Typecheck every clause (and optionally a query) against the signature, collecting
all errors; `none` is returned when any exists. -/
-- @tg: implements:: [[openspec:elpi-typechecker#Load-time type errors with positions]]
def checkProgram (sig : Signature) (clauses : List STm) (query : Option STm := none)
    (known : Std.HashSet String := {}) : Except (List TypeError) Unit :=
  let defined : Std.HashSet String :=
    clauses.foldl (fun s c => match clauseHead c with | some n => s.insert n | none => s) known
  let env : Env := { sig, defined }
  let act : TCM Unit := do
    for c in clauses do
      checkClause env c
    match query with
    | some q => checkClause env q
    | none => pure ()
  let (_, st) := act.run {}
  if st.errors.isEmpty then .ok () else .error st.errors.toList

end Typecheck
end Elpi
