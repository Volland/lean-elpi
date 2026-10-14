import Lean
import Elpi.Core.Index

/-!
# Expr reflection

Lossless translation between `Lean.Expr` and the higher-order abstract syntax `term` of
`lib/elpi/lean.elpi`. Bound variables become ELPI λ-binders, so no de Bruijn index is ever
exposed. Names, binders, universe levels, metadata and metavariable / free-variable ids are
opaque host values (ctypes) whose canonical string encoding is their identity: structurally
equal levels get identical handles and unification compares them by identity only.
-/

-- @lat: [[components#Expr reflection]]

namespace Elpi.Reflect

open _root_.Lean

/-! ### Opaque values -/

def sep : Char := '\u0001'

/-- Length-prefixed string, so encodings nest without escaping. -/
def lp (s : String) : String := s!"{s.length}:{s}"

def nameEnc (n : Name) : String :=
  let rec go : Name → List String
    | .anonymous => []
    | .str p s => go p ++ ["s" ++ s]
    | .num p k => go p ++ [s!"n{k}"]
  String.intercalate (String.singleton sep) (go n)

def nameDec (s : String) : Name :=
  if s.isEmpty then .anonymous else
  (s.splitOn (String.singleton sep)).foldl (fun n c =>
    if c.startsWith "s" then .str n (c.drop 1).toString
    else .num n ((c.drop 1).toString.toNat?.getD 0)) .anonymous

/-- The opaque value of type `ty` with canonical encoding `data`. -/
def mkOpaque (ty data : String) : Term :=
  .builtinData { handle := (hash (ty, data)).toNat, typeName := ty, data }

def nameTerm (n : Name) : Term := mkOpaque "name" (nameEnc n)

/-! #### Levels -/

partial def levelEnc : Level → String
  | .zero => "z"
  | .succ l => "s(" ++ levelEnc l ++ ")"
  | .max a b => "m(" ++ levelEnc a ++ "," ++ levelEnc b ++ ")"
  | .imax a b => "i(" ++ levelEnc a ++ "," ++ levelEnc b ++ ")"
  | .param n => "p" ++ lp (nameEnc n)
  | .mvar id => "v" ++ lp (nameEnc id.name)

/-- Parse a length-prefixed string at `i`. -/
def takeLp (cs : Array Char) (i : Nat) : Option (String × Nat) := do
  let mut j := i
  let mut len := 0
  while j < cs.size && cs[j]!.isDigit do
    len := len * 10 + (cs[j]!.toNat - '0'.toNat)
    j := j + 1
  guard (j < cs.size && cs[j]! == ':')
  j := j + 1
  guard (j + len ≤ cs.size)
  return (String.ofList (cs.extract j (j + len)).toList, j + len)

partial def levelDecAt (cs : Array Char) (i : Nat) : Option (Level × Nat) := do
  let c ← cs[i]?
  match c with
  | 'z' => return (.zero, i + 1)
  | 's' =>
    let (l, j) ← levelDecAt cs (i + 2)
    return (.succ l, j + 1)
  | 'm' | 'i' =>
    let (a, j) ← levelDecAt cs (i + 2)
    let (b, k) ← levelDecAt cs (j + 1)
    return ((if c == 'm' then Level.max a b else Level.imax a b), k + 1)
  | 'p' =>
    let (s, j) ← takeLp cs (i + 1)
    return (.param (nameDec s), j)
  | 'v' =>
    let (s, j) ← takeLp cs (i + 1)
    return (.mvar ⟨nameDec s⟩, j)
  | _ => none

def levelDec (s : String) : Option Level := (levelDecAt s.toList.toArray 0).map (·.1)

/-- Levels are opaque handles: structurally equal levels share one, and ELPI unification
compares handles by identity. -/
-- @tg: implements:: [[openspec:lean-reflection#Opaque universe levels]]
def levelTerm (l : Level) : Term := mkOpaque "level" (levelEnc l)

/-! #### Binders and metadata -/

def binderInfoEnc : BinderInfo → String
  | .default => "0" | .implicit => "1" | .strictImplicit => "2" | .instImplicit => "3"

def binderInfoDec : String → BinderInfo
  | "1" => .implicit | "2" => .strictImplicit | "3" => .instImplicit | _ => .default

def binderTerm (n : Name) (bi : BinderInfo) (nonDep : Bool := false) : Term :=
  mkOpaque "binder" (lp (nameEnc n) ++ binderInfoEnc bi ++ (if nonDep then "1" else "0"))

def binderDec (s : String) : Option (Name × BinderInfo × Bool) := do
  let cs := s.toList.toArray
  let (n, j) ← takeLp cs 0
  let bi ← cs[j]?
  let nd ← cs[j+1]?
  return (nameDec n, binderInfoDec (String.singleton bi), nd == '1')

def dataValueEnc : DataValue → Except String String
  | .ofString s => .ok ("S" ++ lp s)
  | .ofBool b => .ok (if b then "B1" else "B0")
  | .ofName n => .ok ("N" ++ lp (nameEnc n))
  | .ofNat n => .ok ("U" ++ lp (toString n))
  | .ofInt i => .ok ("I" ++ lp (toString i))
  | .ofSyntax _ => .error "metadata holding syntax cannot be reflected"

def mdataEnc (m : MData) : Except String String := do
  let mut out := s!"{m.size};"
  for (k, v) in m do
    out := out ++ lp (nameEnc k) ++ (← dataValueEnc v)
  return out

def mdataDec (s : String) : Option MData := do
  let cs := s.toList.toArray
  let mut i := 0
  let mut cnt := 0
  while i < cs.size && cs[i]!.isDigit do
    cnt := cnt * 10 + (cs[i]!.toNat - '0'.toNat)
    i := i + 1
  guard (i < cs.size && cs[i]! == ';')
  i := i + 1
  let mut m : MData := {}
  for _ in [0:cnt] do
    let (k, j) ← takeLp cs i
    let tag ← cs[j]?
    i := j + 1
    let v ←
      match tag with
      | 'B' => let b ← cs[i]?; i := i + 1; pure (DataValue.ofBool (b == '1'))
      | 'S' => let (x, j) ← takeLp cs i; i := j; pure (DataValue.ofString x)
      | 'N' => let (x, j) ← takeLp cs i; i := j; pure (DataValue.ofName (nameDec x))
      | 'U' => let (x, j) ← takeLp cs i; i := j; pure (DataValue.ofNat (x.toNat?.getD 0))
      | 'I' => let (x, j) ← takeLp cs i; i := j; pure (DataValue.ofInt (x.toInt?.getD 0))
      | _ => none
    m := m.insert (nameDec k) v
  return m

/-! ### Expr → term -/

def listTerm (xs : List Term) : Term :=
  xs.foldr (fun x acc => .app (.const cCons) #[x, acc]) (.const cNil)

def mk (c : ConstId) (args : Array Term) : Term := .app (.const c) args

/-- Decide how unassigned metavariables are reflected. -/
structure ToOpts where
  /-- Map a metavariable to an ELPI clause variable index (quotation holes). -/
  holeOf : MVarId → Option Nat := fun _ => none

/-- Reflect `e`, which will live at ELPI depth `d0`. Loose bound variables are an error. -/
partial def toTermAt (opts : ToOpts) (e : Expr) (d0 : Nat) (k : Nat := 0) : Except String Term := do
  match e with
  | .bvar i =>
    if i < k then return .bound (d0 + k - 1 - i)
    else throw "loose bound variable"
  | .fvar id => return mk cFVarR #[mkOpaque "fvarid" (nameEnc id.name)]
  | .mvar id =>
    match opts.holeOf id with
    | some i => return .cvar i #[]
    | none => return mk cMVarR #[mkOpaque "mvarid" (nameEnc id.name)]
  | .sort l => return mk cSortR #[levelTerm l]
  | .const n us => return mk cConstR #[nameTerm n, listTerm (us.map levelTerm)]
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let h ← toTermAt opts f d0 k
    let as ← args.toList.mapM (toTermAt opts · d0 k)
    return mk cAppR #[h, listTerm as]
  | .lam n t b bi =>
    return mk cFunR #[binderTerm n bi, ← toTermAt opts t d0 k, .lam (← toTermAt opts b d0 (k + 1))]
  | .forallE n t b bi =>
    return mk cForallR #[binderTerm n bi, ← toTermAt opts t d0 k, .lam (← toTermAt opts b d0 (k + 1))]
  | .letE n t v b nd =>
    return mk cLetR #[binderTerm n .default nd, ← toTermAt opts t d0 k, ← toTermAt opts v d0 k,
                      .lam (← toTermAt opts b d0 (k + 1))]
  | .lit (.natVal n) => return mk cLitR #[mk cNatLitR #[.lit (.int n)]]
  | .lit (.strVal s) => return mk cLitR #[mk cStrLitR #[.lit (.str s)]]
  | .mdata m b =>
    return mk cMDataR #[mkOpaque "mdata" (← mdataEnc m), ← toTermAt opts b d0 k]
  | .proj s i b => return mk cProjR #[nameTerm s, .lit (.int i), ← toTermAt opts b d0 k]

/-- Reflect a closed `Expr` at ELPI depth 0. -/
-- @tg: implements:: [[openspec:lean-reflection#HOAS term encoding]]
def toTerm (e : Expr) : Except String Term := toTermAt {} e 0

/-! ### term → Expr -/

def listElems : Term → Except String (List Term)
  | .const c => if c == cNil then .ok [] else .error "list expected"
  | .app (.const c) #[x, xs] =>
    if c == cCons then do return x :: (← listElems xs) else .error "list expected"
  | _ => .error "list expected"

def opaqueOf (ty : String) : Term → Except String String
  | .builtinData o => if o.typeName == ty then .ok o.data else .error s!"{ty} expected"
  | _ => .error s!"{ty} expected"

/-- Reify a (fully dereferenced) `term` living at ELPI depth `d0`. ELPI variables that are
still present are handed to `onVar` (the tactic bridge turns them into metavariables). -/
-- @tg: implements:: [[openspec:lean-reflection#Lossless Expr round trip]]
partial def ofTermAt (onVar : UVarId → Except String Expr) (t : Term) (d0 : Nat) (k : Nat := 0) :
    Except String Expr := do
  let body (b : Term) : Term :=
    match b with
    | .lam x => x
    | f => Term.applyAt (f.shiftUp (d0 + k) 1) #[.bound (d0 + k)] (d0 + k + 1)
  match t with
  | .bound l =>
    if l ≥ d0 && l < d0 + k then return .bvar (d0 + k - 1 - l)
    else throw "an ELPI bound variable escapes its scope"
  | .uvar u args => do
    let h ← onVar u
    return mkAppN h (← args.toList.mapM (ofTermAt onVar · d0 k)).toArray
  | .app (.const c) args =>
    if c == cConstR && args.size == 2 then
      let n := nameDec (← opaqueOf "name" args[0]!)
      let us ← (← listElems args[1]!).mapM fun l => do
        match levelDec (← opaqueOf "level" l) with
        | some l => pure l
        | none => throw "bad level"
      return .const n us
    else if c == cAppR && args.size == 2 then
      let h ← ofTermAt onVar args[0]! d0 k
      let as ← (← listElems args[1]!).mapM (ofTermAt onVar · d0 k)
      return mkAppN h as.toArray
    else if (c == cFunR || c == cForallR) && args.size == 3 then
      let some (n, bi, _) := binderDec (← opaqueOf "binder" args[0]!) | throw "bad binder"
      let ty ← ofTermAt onVar args[1]! d0 k
      let b ← ofTermAt onVar (body args[2]!) d0 (k + 1)
      return if c == cFunR then .lam n ty b bi else .forallE n ty b bi
    else if c == cLetR && args.size == 4 then
      let some (n, _, nd) := binderDec (← opaqueOf "binder" args[0]!) | throw "bad binder"
      let ty ← ofTermAt onVar args[1]! d0 k
      let v ← ofTermAt onVar args[2]! d0 k
      let b ← ofTermAt onVar (body args[3]!) d0 (k + 1)
      return .letE n ty v b nd
    else if c == cSortR && args.size == 1 then
      match levelDec (← opaqueOf "level" args[0]!) with
      | some l => return .sort l
      | none => throw "bad level"
    else if c == cLitR && args.size == 1 then
      match args[0]! with
      | .app (.const c') #[.lit (.int n)] =>
        if c' == cNatLitR && n ≥ 0 then return .lit (.natVal n.toNat) else throw "bad literal"
      | .app (.const c') #[.lit (.str s)] =>
        if c' == cStrLitR then return .lit (.strVal s) else throw "bad literal"
      | _ => throw "bad literal"
    else if c == cMVarR && args.size == 1 then
      return .mvar ⟨nameDec (← opaqueOf "mvarid" args[0]!)⟩
    else if c == cFVarR && args.size == 1 then
      return .fvar ⟨nameDec (← opaqueOf "fvarid" args[0]!)⟩
    else if c == cProjR && args.size == 3 then
      match args[1]! with
      | .lit (.int i) =>
        return .proj (nameDec (← opaqueOf "name" args[0]!)) i.toNat (← ofTermAt onVar args[2]! d0 k)
      | _ => throw "bad projection index"
    else if c == cMDataR && args.size == 2 then
      match mdataDec (← opaqueOf "mdata" args[0]!) with
      | some m => return .mdata m (← ofTermAt onVar args[1]! d0 k)
      | none => throw "bad metadata"
    else throw "not a reflected Lean term"
  | _ => throw "not a reflected Lean term"

def ofTerm (t : Term) (onVar : UVarId → Except String Expr := fun _ => .error "an ELPI variable is left in the term") :
    Except String Expr := ofTermAt onVar t 0

end Elpi.Reflect
