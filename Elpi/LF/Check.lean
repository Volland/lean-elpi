import Std.Data.HashMap
import Elpi.Core.Machine

/-!
# LF checker

LF (λΠ) for `#lf` files: the LF surface syntax read with the ELPI lexer, the canonical
bidirectional checker with reconstruction of implicit arguments, and the signature.

Objects are core terms in β-normal, η-long form (de Bruijn levels, hereditary substitution is
`Term.subst`); types and kinds are the new data. Elaboration turns the positioned surface
syntax into explicit terms: constants are applied to the metavariables of their implicit
arguments, and a declaration's free uppercase variables are abstracted as leading Π's in
order of first occurrence. Unification of objects is the pattern unifier of the core.
-/

-- @lat: [[components#LF checker]]

namespace Elpi.LF

/-- Type families `a M₁ … Mₙ`, `Πx:A. B` (the codomain lives one level deeper) and the
unknown types of reconstruction. -/
inductive LFTy where
  | atom (fam : String) (args : Array Term)
  | pi (n : String) (dom cod : LFTy)
  | unk (id : Nat)
  deriving Inhabited, BEq

inductive LFKind where
  | type
  | pi (n : String) (dom : LFTy) (cod : LFKind)
  deriving Inhabited, BEq

/-- How a family is exported: syntax (`Type`) or judgment (`Prop`). -/
inductive FamRole where
  | syn
  | judgment
  deriving Inhabited, BEq, Repr

/-- A world block: `#block b (params) : x₁:A₁, …, xₖ:Aₖ.` -/
structure Block where
  name : String
  params : Array (String × LFTy)
  entries : Array (String × LFTy)
  deriving Inhabited

structure ModeDecl where
  fam : String
  /-- `true` = input (`+`). -/
  modes : Array (Bool × String)
  deriving Inhabited

structure TotalDecl where
  fam : String
  order : Array Nat
  worlds : Array String
  deriving Inhabited

/-- `#bridge nat = Nat.` and `#bridge add : nat -> nat -> nat = Nat.add.` -/
structure Bridge where
  lfName : String
  leanName : String
  deriving Inhabited

/-- A loaded signature. `consts` holds fully explicit types: the first `implicit c` Π's are
the implicit arguments. -/
structure LFSig where
  name : String := ""
  families : Std.HashMap String (LFKind × FamRole) := {}
  consts : Std.HashMap String LFTy := {}
  implicit : Std.HashMap String Nat := {}
  /-- Declaration order of families and constants (export dependency order). -/
  order : Array String := #[]
  blocks : Std.HashMap String Block := {}
  worlds : Std.HashMap String (Array String) := {}
  modes : Std.HashMap String ModeDecl := {}
  totals : Array TotalDecl := #[]
  /-- The argument names of each `#total` call pattern. -/
  totalArgs : Std.HashMap String (Array String) := {}
  bridges : Std.HashMap String Bridge := {}
  strategy : Option (String × Option Nat) := none
  /-- Positions of declarations, for diagnostics. -/
  positions : Std.HashMap String Pos := {}
  deriving Inhabited

structure LFError where
  decl : String
  pos : Pos
  msg : String
  deriving Inhabited

def LFError.toString (e : LFError) : String :=
  let d := if e.decl.isEmpty then "" else s!"in declaration '{e.decl}': "
  s!"{e.pos.toString}: {d}{e.msg}"

instance : ToString LFError := ⟨LFError.toString⟩

def cst (n : String) : Term := .const (constIdOf n)

/-! ### Types: substitution and relocation -/

def LFTy.mapTerms (f : Term → Term) : LFTy → LFTy
  | .atom a as => .atom a (as.map f)
  | .pi n d c => .pi n (d.mapTerms f) (c.mapTerms f)
  | .unk i => .unk i

def LFKind.mapTerms (f : Term → Term) : LFKind → LFKind
  | .type => .type
  | .pi n d c => .pi n (d.mapTerms f) (c.mapTerms f)

/-- Substitute `v` (living at depth `d`) for level `d` in a type that lives at depth `d+1+k`. -/
def LFTy.subst (t : LFTy) (d : Nat) (v : Term) : Nat → LFTy
  | k => match t with
    | .atom a as => .atom a (as.map fun x => Term.subst x d v k)
    | .pi n dom cod => .pi n (dom.subst d v k) (cod.subst d v (k + 1))
    | .unk i => .unk i

def LFKind.subst (t : LFKind) (d : Nat) (v : Term) : Nat → LFKind
  | k => match t with
    | .type => .type
    | .pi n dom cod => .pi n (dom.subst d v k) (cod.subst d v (k + 1))

/-- Move a type that lives at depth `from` to depth `to` (its internal binders shift). -/
def LFTy.reloc (t : LFTy) (from_ to : Nat) : LFTy :=
  if to ≤ from_ then t else t.mapTerms (·.shiftUp from_ (to - from_))

def LFKind.reloc (t : LFKind) (from_ to : Nat) : LFKind :=
  if to ≤ from_ then t else t.mapTerms (·.shiftUp from_ (to - from_))

/-! ### Printing -/

structure Names where
  syms : Symbols

def ppTm (syms : Symbols) (store : Store) (t : Term) (d : Nat) : String :=
  (Print.pp t d 1000 false).run' { syms, store }

partial def LFTy.pp (syms : Symbols) (store : Store) (d : Nat) : LFTy → String
  | .atom a as =>
    if as.isEmpty then a else a ++ " " ++ " ".intercalate (as.toList.map fun t => ppTm syms store t d)
  | .pi n dom cod =>
    let used := n != "_"
    let ds := match dom with
      | .pi .. => "(" ++ dom.pp syms store d ++ ")"
      | _ => dom.pp syms store d
    if used then s!"pi {n}:{dom.pp syms store d}\\ {cod.pp syms store (d + 1)}"
    else s!"{ds} -> {cod.pp syms store (d + 1)}"
  | .unk i => s!"?{i}"

/-! ### Surface syntax -/

namespace LFSyntax

open Elpi.Parser

structure PS where
  toks : Array Token
  i : Nat := 0

abbrev PM := StateT PS (Except ParseError)

def peek : PM Token := do return (← get).toks[(← get).i]!
def advance : PM Unit := modify fun s => { s with i := min (s.i + 1) (s.toks.size - 1) }
def failAt {α : Type} (p : Pos) (m : String) : PM α := throw { pos := p, msg := m }

def expectTok (t : Tok) : PM Unit := do
  let k ← peek
  if k.tok == t then advance else failAt k.pos s!"expected '{tokDesc t}' but found '{tokDesc k.tok}'"

mutual
/-- `A -> B` (right associative) and `B <- A` (left associative). -/
partial def parseTy : PM STm := do
  let mut lhs ← parseApp
  repeat
    let t ← peek
    if t.tok == .sym "->" then
      advance
      let rhs ← parseTy
      lhs := .app (.const "->" t.pos) [lhs, rhs] t.pos
    else if t.tok == .sym "<-" then
      advance
      let rhs ← parseApp
      lhs := .app (.const "->" t.pos) [rhs, lhs] t.pos
    else break
  return lhs

partial def parseApp : PM STm := do
  let h ← parseAtom
  let mut args : Array STm := #[]
  repeat
    let t ← peek
    match t.tok with
    | .ident _ | .var _ | .lp | .bind _ | .int _ => args := args.push (← parseAtom)
    | _ => break
  if args.isEmpty then return h else return .app h args.toList h.pos

partial def parseAtom : PM STm := do
  let t ← peek
  match t.tok with
  | .ident "pi" =>
    -- `pi x:A\ B`
    let n ← do advance; peek
    let x ← match n.tok with
      | .ident s | .var s => do advance; pure s
      | _ => failAt n.pos "variable expected after 'pi'"
    expectTok (.sym ":")
    -- the domain ends at `\`; a trailing `a\` lexes as one binder token
    let mut parts : Array STm := #[]
    let mut done := false
    while !done do
      let k ← peek
      match k.tok with
      | .bind s => advance; parts := parts.push (.const s k.pos); done := true
      | .sym "\\" => advance; done := true
      | .ident _ | .var _ | .lp => parts := parts.push (← parseAtom)
      | _ => failAt k.pos "'\\' expected after the domain of 'pi'"
    if parts.isEmpty then failAt t.pos "domain expected"
    let dom := if parts.size == 1 then parts[0]! else STm.app parts[0]! (parts.toList.drop 1) t.pos
    let body ← parseTy
    return .app (.const "Π" t.pos) [dom, .lam x body t.pos] t.pos
  | .ident s => advance; return .const s t.pos
  | .var s => advance; return .var s t.pos
  | .int i => advance; return .int i t.pos
  | .bind x => advance; let b ← parseTy; return .lam x b t.pos
  | .lp =>
    advance
    let e ← parseTy
    expectTok .rp
    return e
  | k => failAt t.pos s!"term expected, found '{tokDesc k}'"
end

/-- A directive `# name args .` as its tokens. -/
structure Directive where
  name : String
  toks : Array Token
  pos : Pos

inductive Item where
  | decl (name : String) (ty : STm) (pos : Pos)
  | directive (d : Directive)

/-- Read an `#lf` file: the header, then declarations and directives. -/
def parseLF (file src : String) : Except ParseError (Array Item) := do
  let toks ← lex file src
  let run : PM (Array Item) := do
    let h1 ← peek
    unless h1.tok == .sym "#" do failAt h1.pos "an LF file must start with '#lf'"
    advance
    let h2 ← peek
    unless h2.tok == .ident "lf" do failAt h2.pos "an LF file must start with '#lf'"
    advance
    let mut items : Array Item := #[]
    repeat
      let t ← peek
      if t.tok == .eof then break
      match t.tok with
      | .sym "#" =>
        advance
        let n ← peek
        let .ident name := n.tok | failAt n.pos "directive name expected after '#'"
        advance
        let mut ts : Array Token := #[]
        repeat
          let k ← peek
          if k.tok == .dot || k.tok == .eof then break
          ts := ts.push k
          advance
        expectTok .dot
        items := items.push (.directive { name, toks := ts, pos := t.pos })
      | .ident name =>
        advance
        expectTok (.sym ":")
        let ty ← parseTy
        expectTok .dot
        items := items.push (.decl name ty t.pos)
      | k => failAt t.pos s!"declaration or directive expected, found '{tokDesc k}'"
    return items
  let (items, _) ← run.run { toks }
  return items

/-- A single type expression (for queries). -/
def parseTyString (file src : String) : Except ParseError STm := do
  let toks ← lex file src
  let (t, st) ← (do
      let t ← parseTy
      let k ← peek
      if k.tok == .dot then advance
      pure t : PM STm).run { toks }
  let k := st.toks[st.i]!
  if k.tok != .eof then throw { pos := k.pos, msg := s!"unexpected '{tokDesc k.tok}'" }
  return t

/-- Does this source start with the `#lf` header (after comments)? -/
def isLF (file src : String) : Bool :=
  match lex file src with
  | .ok toks => toks.size ≥ 2 && toks[0]!.tok == .sym "#" && toks[1]!.tok == .ident "lf"
  | .error _ => false

end LFSyntax

/-! ### Elaboration -/

structure CS where
  store : Store := {}
  /-- Types of the object metavariables. -/
  metaTy : Std.HashMap Nat LFTy := {}
  tyMetas : Array (Option LFTy) := #[]
  /-- Named (uppercase) variables of the declaration, in order of first occurrence. -/
  named : Array (String × UVarId) := #[]
  decl : String := ""

abbrev CM := StateT CS (Except LFError)

structure Env where
  sig : LFSig
  /-- Bound names, innermost first, with their level. -/
  names : List (String × Nat) := []
  /-- Types of the bound variables; the type of level `l` lives at depth `l`. -/
  ctx : Array LFTy := #[]

def Env.depth (e : Env) : Nat := e.ctx.size

def Env.bind (e : Env) (n : String) (ty : LFTy) : Env :=
  { e with names := (n, e.ctx.size) :: e.names, ctx := e.ctx.push ty }

def errAt {α : Type} (p : Pos) (msg : String) : CM α := do
  throw { decl := (← get).decl, pos := p, msg }

def freshTyMeta : CM LFTy := do
  let s ← get
  set { s with tyMetas := s.tyMetas.push none }
  return .unk s.tyMetas.size

partial def resTy (t : LFTy) : CM LFTy := do
  match t with
  | .unk i =>
    match (← get).tyMetas[i]! with
    | some t' => resTy t'
    | none => return t
  | t => return t

def freshObjMeta (ty : LFTy) (name? : Option String := none) : CM Term := do
  let s ← get
  let (u, store) := s.store.fresh 0 name?
  set { s with store, metaTy := s.metaTy.insert u.idx ty }
  return .uvar u #[]

def prn (env : Env) (t : LFTy) : CM String := do
  let s ← get
  let syms := env.sig.order.foldl (fun sy n => (sy.intern n).2) Symbols.initial
  return LFTy.pp syms s.store env.depth t

mutual
/-- Unify two types at depth `d`. -/
partial def unifyTy (d : Nat) (a b : LFTy) : CM Bool := do
  let a ← resTy a
  let b ← resTy b
  match a, b with
  | .unk i, .unk j =>
    if i == j then return true
    modify fun s => { s with tyMetas := s.tyMetas.set! i (some b) }
    return true
  | .unk i, t | t, .unk i =>
    modify fun s => { s with tyMetas := s.tyMetas.set! i (some t) }
    return true
  | .atom f as, .atom g bs =>
    if f != g || as.size != bs.size then return false
    for i in [0:as.size] do
      let s ← get
      match unify s.store as[i]! bs[i]! d with
      | some st => set { s with store := st }
      | none => return false
    return true
  | .pi _ d1 c1, .pi _ d2 c2 => return (← unifyTy d d1 d2) && (← unifyTy (d + 1) c1 c2)
  | _, _ => return false
end

/-- Instantiate the codomain of a Π type with `a` (the type lives at depth `d`). -/
def instCod (cod : LFTy) (d : Nat) (a : Term) : LFTy := cod.subst d a 0

/-- The type of a head, relocated to the current depth. -/
def headType (env : Env) (h : STm) : CM (Option (Term × LFTy × Nat)) := do
  let m := env.depth
  match h with
  | .const n _ =>
    match env.names.lookup n with
    | some l => return some (.bound l, env.ctx[l]!.reloc l m, 0)
    | none =>
      match env.sig.consts[n]? with
      | some t => return some (cst n, t.reloc 0 m, env.sig.implicit.getD n 0)
      | none => return none
  | _ => return none

/-- Bind the named variable `X` of the declaration (created at its first occurrence). -/
def namedMeta (x : String) : CM (Term × LFTy) := do
  let s ← get
  match s.named.find? (·.1 == x) with
  | some (_, u) => return (.uvar u #[], s.metaTy[u.idx]!)
  | none =>
    let ty ← freshTyMeta
    let t ← freshObjMeta ty (some x)
    let s ← get
    let .uvar u _ := t | unreachable!
    set { s with named := s.named.push (x, u) }
    return (t, ty)

mutual
/-- Check `s` against `exp`; the result is the explicit, canonical term. -/
partial def elabObj (env : Env) (s : STm) (exp : LFTy) : CM Term := do
  let m := env.depth
  match ← resTy exp with
  | .pi n dom cod =>
    match s with
    | .lam x b _ => return .lam (← elabObj (env.bind x dom) b cod)
    | _ =>
      -- a non-λ at function type: η-expand if its type is a function type
      let saved ← get
      let (t0, ty) ← inferObj env s
      let ty' ← resTy ty
      match ty' with
      | .unk _ =>
        -- a variable of not yet known type takes the expected function type
        if ← unifyTy m ty exp then return t0
        else errAt s.pos "type mismatch"
      | .pi .. =>
        set saved
        let e' := env.bind s!"%eta{m}" dom
        let app := STm.app s [.const s!"%eta{m}" s.pos] s.pos
        return .lam (← elabObj e' app cod)
      | _ =>
        set saved
        errAt s.pos s!"expected an object of type {← prn env exp} but found one of type {← prn env ty}"
  | .atom f as =>
    match s with
    | .lam _ _ p => errAt p s!"a λ cannot have the atomic type {← prn env exp}"
    | _ =>
      let (t, ty) ← inferObj env s
      if ← unifyTy m ty exp then return t
      else errAt s.pos s!"expected type {← prn env exp} but found {← prn env ty}"
  | .unk i =>
    let (t, ty) ← inferObj env s
    if ← unifyTy m ty exp then return t
    else errAt s.pos "type mismatch"

partial def inferObj (env : Env) (s : STm) : CM (Term × LFTy) := do
  let m := env.depth
  -- flatten the application spine
  let rec spine : STm → STm × List STm
    | .app f as _ => let (h, bs) := spine f; (h, bs ++ as)
    | t => (t, [])
  let (h, args) := spine s
  match h with
  | .var x p =>
    let (t, ty) ← namedMeta x
    applyArgs env t ty args
  | .int i p =>
    -- a numeral has the type bridged to Lean's `Nat`
    match env.sig.bridges.toList.find? (fun (n, b) => b.leanName == "Nat" && env.sig.families.contains n) with
    | some (fam, _) => return (Term.lit (.int i), .atom fam #[])
    | none => errAt p "numerals need a type bridged to Nat (#bridge nat = Nat)"
  | .lam _ _ p => errAt p "cannot infer the type of a λ here"
  | .const n p =>
    match ← headType env h with
    | none => errAt p s!"undeclared constant {n}"
    | some (head, ty, nImp) =>
      -- implicit arguments become metavariables
      let mut ty := ty
      let mut head := head
      let mut implArgs : Array Term := #[]
      for _ in [0:nImp] do
        match ← resTy ty with
        | .pi _ dom cod =>
          let mv ← freshObjMeta dom
          implArgs := implArgs.push mv
          ty := instCod cod m mv
        | _ => errAt p "internal: missing implicit argument"
      applyArgs env (Term.mkApp head implArgs) ty args
  | other => errAt other.pos "an application head must be a constant or a variable"

partial def applyArgs (env : Env) (head : Term) (ty : LFTy) (args : List STm) : CM (Term × LFTy) := do
  let m := env.depth
  let mut t := head
  let mut ty := ty
  let mut done : Array Term := #[]
  for a in args do
    match ← resTy ty with
    | .pi _ dom cod =>
      let a' ← elabObj env a dom
      done := done.push a'
      ty := instCod cod m a'
    | .unk i =>
      -- an unknown function type: give it the shape `Πx:A. ?B`
      let (a', ta) ← inferObj env a
      let cod ← freshTyMeta
      modify fun s => { s with tyMetas := s.tyMetas.set! i (some (.pi "_" ta cod)) }
      done := done.push a'
      ty := cod
    | .atom .. =>
      errAt a.pos s!"too many arguments: the head has type {← prn env ty}, which takes no more"
  return (Term.mkApp t done, ty)
end

mutual
/-- A well-formed type. -/
partial def elabTy (env : Env) (s : STm) : CM LFTy := do
  let m := env.depth
  match s with
  | .app (.const "->" _) [a, b] _ =>
    let a' ← elabTy env a
    let b' ← elabTy (env.bind "_" a') b
    return .pi "_" a' b'
  | .app (.const "Π" _) [dom, .lam x body _] _ =>
    let d' ← elabTy env dom
    let b' ← elabTy (env.bind x d') body
    return .pi x d' b'
  | _ =>
    let rec spine : STm → STm × List STm
      | .app f as _ => let (h, bs) := spine f; (h, bs ++ as)
      | t => (t, [])
    let (h, args) := spine s
    match h with
    | .const fam p =>
      match env.sig.families[fam]? with
      | none => errAt p s!"undeclared type family {fam}"
      | some (k, _) =>
        let mut k := k.reloc 0 m
        let mut out : Array Term := #[]
        for a in args do
          match k with
          | .pi _ dom kc =>
            let a' ← elabObj env a dom
            out := out.push a'
            k := kc.subst m a' 0
          | .type => errAt a.pos s!"the family {fam} takes no more arguments"
        match k with
        | .type => return .atom fam out
        | .pi .. => errAt p s!"the family {fam} expects more arguments"
    | other => errAt other.pos "a type was expected"

partial def elabKind (env : Env) (s : STm) : CM LFKind := do
  match s with
  | .const "type" _ => return .type
  | .app (.const "->" _) [a, b] _ =>
    let a' ← elabTy env a
    let b' ← elabKind (env.bind "_" a') b
    return .pi "_" a' b'
  | .app (.const "Π" _) [dom, .lam x body _] _ =>
    let d' ← elabTy env dom
    let b' ← elabKind (env.bind x d') body
    return .pi x d' b'
  | other => errAt other.pos "a kind was expected (type, or a Π / arrow ending in type)"
end

/-- Does the declared type end in `type` (so it declares a family)? -/
partial def isKindExpr : STm → Bool
  | .const "type" _ => true
  | .app (.const "->" _) [_, b] _ => isKindExpr b
  | .app (.const "Π" _) [_, .lam _ b _] _ => isKindExpr b
  | _ => false

/-! ### Abstracting the metavariables -/

/-- Unassigned variables of a zonked term, in order of first occurrence. -/
partial def termMetas (store : Store) (t : Term) (acc : Array UVarId) : Array UVarId :=
  match store.deref t 0 with
  | .uvar u as => as.foldl (fun a x => termMetas store x a) (if acc.contains u then acc else acc.push u)
  | .app h as => as.foldl (fun a x => termMetas store x a) (termMetas store h acc)
  | .lam b => termMetas store b acc
  | _ => acc

partial def tyMetasOf (store : Store) (t : LFTy) (acc : Array UVarId) : Array UVarId :=
  match t with
  | .atom _ as => as.foldl (fun a x => termMetas store x a) acc
  | .pi _ d c => tyMetasOf store c (tyMetasOf store d acc)
  | .unk _ => acc

/-- Replace the collected variables by bound levels and shift internal binders by `n`. -/
partial def abstractTerm (store : Store) (ms : Array UVarId) (n : Nat) (t : Term) : Term :=
  match store.deref t 0 with
  | .uvar u as =>
    let as' := as.map (abstractTerm store ms n)
    match ms.findIdx? (· == u) with
    | some i => Term.mkApp (.bound i) as'
    | none => .uvar u as'
  | .bound l => .bound (l + n)
  | .app h as => .app (abstractTerm store ms n h) (as.map (abstractTerm store ms n))
  | .lam b => .lam (abstractTerm store ms n b)
  | t => t

partial def abstractTy (store : Store) (ms : Array UVarId) (n : Nat) : LFTy → LFTy
  | .atom a as => .atom a (as.map (abstractTerm store ms n))
  | .pi x d c => .pi x (abstractTy store ms n d) (abstractTy store ms n c)
  | .unk i => .unk i

/-- Resolve type metavariables (replace by their value). -/
partial def zonkTy (tm : Array (Option LFTy)) : LFTy → LFTy
  | .unk i => match tm[i]! with | some t => zonkTy tm t | none => .unk i
  | .pi x d c => .pi x (zonkTy tm d) (zonkTy tm c)
  | t => t

partial def hasTyMeta : LFTy → Bool
  | .unk _ => true
  | .pi _ d c => hasTyMeta d || hasTyMeta c
  | _ => false

/-- Close a type: its remaining metavariables become implicit Π's, in order of first
occurrence; returns the closed type and the number of implicit arguments. A variable whose
type cannot be determined is an error naming it. -/
def closeType (env : Env) (ty : LFTy) (p : Pos) : CM (LFTy × Nat) := do
  let s ← get
  let ty := zonkTy s.tyMetas ty
  -- collect: for each variable, the variables in its type first
  let rec collect (u : UVarId) (acc : Array UVarId) (fuel : Nat) : Array UVarId :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if acc.contains u then acc else
      let tyU := match s.metaTy[u.idx]? with | some t => zonkTy s.tyMetas t | none => .unk 0
      let deps := tyMetasOf s.store tyU #[]
      let acc := deps.foldl (fun a d => collect d a f) acc
      acc.push u
  -- named variables first (in textual order of first occurrence), then the anonymous ones
  let direct := tyMetasOf s.store ty #[]
  let namedFirst := (s.named.filterMap fun (_, u) => if direct.contains u then some u else none)
  let ordered := namedFirst ++ direct.filter fun u => !namedFirst.contains u
  let ms := ordered.foldl (fun a u => collect u a 64) #[]
  let n := ms.size
  let mut out := abstractTy s.store ms n ty
  -- wrap the implicit Π's, innermost last
  let mut tys : Array (String × LFTy) := #[]
  for i in [0:n] do
    let u := ms[i]!
    let tyU := zonkTy s.tyMetas (s.metaTy[u.idx]?.getD (.unk 0))
    let name := (s.named.find? (·.2 == u)).map (·.1) |>.getD s!"_{i}"
    if hasTyMeta tyU then
      throw { decl := s.decl, pos := p, msg := s!"cannot determine the type of the variable {name}" }
    tys := tys.push (name, abstractTy s.store (ms.extract 0 i) i tyU)
  for i in (List.range n).reverse do
    let (nm, a) := tys[i]!
    out := .pi nm a out
  return (out, n)

/-! ### Declarations -/

/-- Uppercase variables of a surface term with their positions. -/
partial def textVars : STm → Array (String × Pos) → Array (String × Pos)
  | .var x p, acc => acc.push (x, p)
  | .app f as _, acc => as.foldl (fun a t => textVars t a) (textVars f acc)
  | .lam _ b _, acc => textVars b acc
  | _, acc => acc

/-- Check one declaration and add it to the signature. -/
def checkDecl (sig : LFSig) (name : String) (ty : STm) (p : Pos) : Except LFError LFSig := do
  if sig.families.contains name || sig.consts.contains name then
    throw { decl := name, pos := p, msg := s!"{name} is already declared" }
  let env : Env := { sig }
  let st : CS := { decl := name }
  if isKindExpr ty then
    let (k, _) ← (elabKind env ty).run st
    return { sig with families := sig.families.insert name (k, .judgment),
                      order := sig.order.push name, positions := sig.positions.insert name p }
  else
    -- implicit variables are ordered by their first occurrence in the source text
    let sorted := (textVars ty #[]).qsort (fun a b =>
      a.2.line < b.2.line || (a.2.line == b.2.line && a.2.col < b.2.col))
    let vars := sorted.foldl (fun (acc : Array (String × Pos)) v =>
      if acc.any (·.1 == v.1) then acc else acc.push v) #[]
    let (r, _) ← (do
        for (x, _) in vars do
          let _ ← namedMeta x
        let t ← elabTy env ty
        closeType env t p).run st
    let (t, n) := r
    return { sig with consts := sig.consts.insert name t, implicit := sig.implicit.insert name n,
                      order := sig.order.push name, positions := sig.positions.insert name p }

/-- Elaborate a query type against a signature; the result keeps its metavariables. -/
def elabQueryType (sig : LFSig) (stm : STm) : Except LFError (LFTy × CS) := do
  let env : Env := { sig }
  let st : CS := { decl := "<query>" }
  let sorted := (textVars stm #[]).qsort (fun a b =>
    a.2.line < b.2.line || (a.2.line == b.2.line && a.2.col < b.2.col))
  let (t, st') ← (do
      for (x, _) in sorted do
        let _ ← namedMeta x
      elabTy env stm).run st
  return (t, st')

/-- The positions of the implicit variables aside, the final explicit type of a constant. -/
def LFSig.constType? (sig : LFSig) (n : String) : Option LFTy := sig.consts[n]?

/-- Family roles: a family is a syntax family when some family has it as the type of an
index argument; the others are judgments. -/
partial def inferRoles (sig : LFSig) : LFSig := Id.run do
  let mut syn : Std.HashSet String := {}
  let rec heads : LFTy → List String
    | .atom a _ => [a]
    | .pi _ d c => heads d ++ heads c
    | .unk _ => []
  let rec kindDoms : LFKind → List LFTy
    | .type => []
    | .pi _ d c => d :: kindDoms c
  for (_, (k, _)) in sig.families.toList do
    for d in kindDoms k do
      for h in heads d do syn := syn.insert h
  let fams := sig.families.fold (init := sig.families) fun m n (k, _) =>
    m.insert n (k, if syn.contains n then .syn else .judgment)
  let fams := sig.bridges.fold (init := fams) fun m n _ =>
    match m[n]? with | some (k, _) => m.insert n (k, .syn) | none => m
  return { sig with families := fams }

/-- Load an `#lf` source: declarations are checked in order; directives are recorded. -/
-- @tg: implements:: [[openspec:elpi-lf#Dependent signatures]]
def loadSource (name file src : String) : Except LFError LFSig := do
  let items ← match LFSyntax.parseLF file src with
    | .ok items => pure items
    | .error e => throw { decl := "", pos := e.pos, msg := e.msg }
  let mut sig : LFSig := { name }
  for it in items do
    match it with
    | .decl n ty p => sig ← checkDecl sig n ty p
    | .directive d =>
      match d.name with
      | "strategy" =>
        match d.toks.toList.map (·.tok) with
        | [Parser.Tok.ident "dfs"] => sig := { sig with strategy := some ("dfs", none) }
        | [Parser.Tok.ident "iddfs"] => sig := { sig with strategy := some ("iddfs", none) }
        | [Parser.Tok.ident "bounded", Parser.Tok.int n] => sig := { sig with strategy := some ("bounded", some n.toNat) }
        | _ => throw { decl := "", pos := d.pos, msg := "#strategy expects dfs, iddfs or bounded <n>" }
      | "mode" =>
        let toks := d.toks.toList.map (·.tok)
        match toks with
        | Parser.Tok.ident f :: rest =>
          let rec go : List Parser.Tok → Except LFError (Array (Bool × String))
            | [] => pure #[]
            | Parser.Tok.sym m :: Parser.Tok.var x :: r => do
              if m != "+" && m != "-" then throw { decl := "", pos := d.pos, msg := "#mode: expected + or -" }
              return (#[(m == "+", x)] ++ (← go r))
            | _ => throw { decl := "", pos := d.pos, msg := "#mode expects + or - before each argument name" }
          let ms ← go rest
          sig := { sig with modes := sig.modes.insert f { fam := f, modes := ms } }
        | _ => throw { decl := "", pos := d.pos, msg := "#mode expects a family name" }
      | "total" =>
        let toks := d.toks.toList.map (·.tok)
        let nameOf : Parser.Tok → Option String
          | .ident s | .var s => some s
          | _ => none
        let (before, rest) := toks.span (fun t => t != Parser.Tok.lp)
        match rest with
        | Parser.Tok.lp :: Parser.Tok.ident f :: args =>
          let args := (args.takeWhile (· != Parser.Tok.rp)).filterMap nameOf
          let ord := before.filterMap nameOf
          let idx := (args.zipIdx.filterMap fun (a, i) => if ord.contains a then some i else none).toArray
          if idx.isEmpty then throw { decl := "", pos := d.pos, msg := "#total: the order must name an argument of the call pattern" }
          sig := { sig with totals := sig.totals.push { fam := f, order := idx, worlds := #[] },
                            totalArgs := sig.totalArgs.insert f args.toArray }
        | _ => throw { decl := "", pos := d.pos, msg := "#total expects `<order> (<family> <args>)`" }
      | "block" =>
        let toks := d.toks.toList.map (·.tok)
        match toks with
        | Parser.Tok.ident b :: Parser.Tok.lp :: rest =>
          let (ps, rest) := rest.span (fun t => t != Parser.Tok.rp)
          let rec pairs : List Parser.Tok → List (String × String)
            | Parser.Tok.var x :: Parser.Tok.sym ":" :: Parser.Tok.ident f :: r
            | Parser.Tok.ident x :: Parser.Tok.sym ":" :: Parser.Tok.ident f :: r => (x, f) :: pairs r
            | _ :: r => pairs r
            | [] => []
          let params := (pairs ps).map fun (x, f) => (x, LFTy.atom f #[])
          let rest := rest.drop 1
          let rest := match rest with | Parser.Tok.sym ":" :: r => r | r => r
          -- entries `x:tm, u:of x T`: the family is the first identifier after the colon
          let groups : List (List Parser.Tok) :=
            (rest.foldl (fun (acc : List (List Parser.Tok)) t =>
              if t == Parser.Tok.comma then [] :: acc
              else match acc with
                | g :: gs => (g ++ [t]) :: gs
                | [] => [[t]]) [[]]).reverse
          let entries : List (String × String) := groups.filterMap fun g =>
            match g with
            | Parser.Tok.var x :: Parser.Tok.sym ":" :: Parser.Tok.ident f :: _
            | Parser.Tok.ident x :: Parser.Tok.sym ":" :: Parser.Tok.ident f :: _ => some (x, f)
            | _ => none
          let es := entries.map fun (x, f) => (x, LFTy.atom f #[])
          let blk : Block := { name := b, params := params.toArray, entries := es.toArray }
          sig := { sig with blocks := sig.blocks.insert b blk }
        | _ => throw { decl := "", pos := d.pos, msg := "#block expects `<name> (<params>) : <entries>`" }
      | "worlds" =>
        let toks := d.toks.toList.map (·.tok)
        match toks with
        | Parser.Tok.lp :: r =>
          let (bs, r) := r.span (fun t => t != Parser.Tok.rp)
          let bs := bs.filterMap fun | Parser.Tok.ident b => some b | _ => none
          match r.drop 1 with
          | Parser.Tok.lp :: Parser.Tok.ident f :: _ =>
            sig := { sig with worlds := sig.worlds.insert f bs.toArray }
          | _ => throw { decl := "", pos := d.pos, msg := "#worlds expects `(<blocks>) (<family> <args>)`" }
        | _ => throw { decl := "", pos := d.pos, msg := "#worlds expects `(<blocks>) (<family> <args>)`" }
      | "bridge" =>
        let toks := d.toks.toList.map (·.tok)
        let isEq : Parser.Tok → Bool := fun t => t == Parser.Tok.sym "="
        let (lhs, rhs) := toks.span (fun t => !isEq t)
        let rhsName := match rhs.drop 1 with
          | [Parser.Tok.ident s] | [Parser.Tok.var s] => some s
          | _ => none
        match lhs, rhsName with
        | [Parser.Tok.ident n], some l =>
          -- a type bridged to a Lean type: declared here as a syntax family
          sig := { sig with families := sig.families.insert n (.type, .syn), order := sig.order.push n,
                            positions := sig.positions.insert n d.pos,
                            bridges := sig.bridges.insert n { lfName := n, leanName := l } }
        | Parser.Tok.ident n :: Parser.Tok.sym ":" :: tyToks, some l =>
          -- a function bridged to a Lean function: declared here as a constant
          let segs := tyToks.foldl (fun (acc : List (List Parser.Tok)) t =>
            if t == Parser.Tok.sym "->" then [] :: acc
            else match acc with | g :: gs => (g ++ [t]) :: gs | [] => [[t]]) [[]] |>.reverse
          let fams := segs.filterMap fun | [Parser.Tok.ident f] => some f | _ => none
          if fams.length != segs.length || fams.isEmpty then
            throw { decl := n, pos := d.pos, msg := "#bridge: the type of a bridged function must be `A1 -> … -> B` over bridged families" }
          let ty := fams.dropLast.foldr (fun f acc => LFTy.pi "_" (.atom f #[]) acc) (LFTy.atom fams.getLast! #[])
          sig := { sig with consts := sig.consts.insert n ty, implicit := sig.implicit.insert n 0,
                            order := sig.order.push n, positions := sig.positions.insert n d.pos,
                            bridges := sig.bridges.insert n { lfName := n, leanName := l } }
        | _, _ => throw { decl := "", pos := d.pos, msg := "#bridge expects `<lf> = <Lean>` or `<c> : <A> = <LeanFn>`" }
      | other => throw { decl := "", pos := d.pos, msg := s!"unknown directive #{other}" }
  return inferRoles sig

end Elpi.LF
