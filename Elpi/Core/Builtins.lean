import Std.Data.HashMap
import Elpi.Core.Store
import Elpi.Core.Index
import Elpi.Core.Typecheck

/-!
# Core builtins

Builtin predicates, the term printer (OCaml-compatible formatting of terms, floats and
strings so output matches the oracle), arithmetic evaluation and the core builtin table.
-/

-- @lat: [[components#Core builtins]]

namespace Elpi

/-- Where `print` output goes: stdout in `IO`, discarded in pure monads. -/
class Output (m : Type → Type) where
  write : String → m Unit

instance : Output IO := ⟨fun s => IO.print s⟩
instance : Output Id := ⟨fun _ => pure ()⟩
instance {ρ : Type} : Output (StateM ρ) := ⟨fun _ => pure ()⟩

/-- Signature of a builtin predicate: name, argument modes and type. -/
structure BuiltinSig where
  name : String
  modes : Array Mode
  type : Ty
  deriving Inhabited

/-- What a builtin sees of the machine. -/
structure BCtx where
  syms : Symbols
  store : Store
  depth : Nat

/-- Outcome of calling a builtin: failure, a runtime error, or lazy alternatives (each a
full argument tuple to be unified with the goal's arguments) over an updated store. -/
inductive BResult where
  | fail
  | error (msg : String)
  | alts (s : Store) (l : LazyList (Array Term))

/-- A builtin predicate in host monad `m`: inputs are dereferenced by the machine; the
effect happens once at call time, the alternatives are a pure lazy list. -/
-- @tg: implements:: [[openspec:elpi-solver-api#Lean builtin predicates]]
structure Builtin (m : Type → Type) where
  sig : BuiltinSig
  run : BCtx → Array Term → m BResult

/-- Build a builtin from a function that returns, for each alternative, the values of the
output-mode arguments only (in order); the machine's tuple convention is filled in. -/
def Builtin.ofOutputs {m : Type → Type} [Monad m] (sig : BuiltinSig)
    (f : BCtx → Array Term → m (LazyList (Array Term))) : Builtin m :=
  { sig
    run := fun c args => do
      let alts ← f c args
      let rec expand : LazyList (Array Term) → LazyList (Array Term)
        | .nil => .nil
        | .cons outs tl =>
          let full := Id.run do
            let mut k := 0
            let mut out : Array Term := #[]
            for i in [0:args.size] do
              if sig.modes.getD i Mode.o == Mode.o then
                out := out.push (outs.getD k args[i]!)
                k := k + 1
              else out := out.push args[i]!
            return out
          .cons full (Thunk.mk fun _ => expand tl.get)
      return .alts c.store (expand alts) }

namespace Print

def fmtFloat (f : Float) : String :=
  -- OCaml `Printf "%f"`: six decimals
  if f.isNaN then "nan"
  else if f.isInf then (if f < 0 then "neg_infinity" else "infinity")
  else
    let neg := f < 0
    let a := if neg then -f else f
    let scaled := (a * 1000000.0 + 0.5).floor
    let n := scaled.toUInt64.toNat
    let ip := n / 1000000
    let fp := n % 1000000
    let fs := toString fp
    let fs := String.ofList (List.replicate (6 - fs.length) '0') ++ fs
    (if neg then "-" else "") ++ toString ip ++ "." ++ fs

/-- Operator precedence info `(prec, leftCtx, rightCtx)` for printing. -/
def opInfo (s : String) : Option (Nat × Nat × Nat) :=
  Parser.infixInfo s

def isOpName (s : String) : Bool := (opInfo s).isSome

structure PS where
  syms : Symbols
  store : Store

abbrev PM := StateM PS

def varName (u : UVarId) : PM String := do
  let s ← get
  match s.store.names.find? u with
  | some n => return s!"X{n}"
  | none =>
    let n := s.store.nameCount
    set { s with store := { s.store with names := s.store.names.insert u n, nameCount := n + 1 } }
    return s!"X{n}"

def cname (c : ConstId) : PM String := return (← get).syms.name c

mutual
/-- Print `t` at depth `d` in a context requiring precedence at least `ctx`. -/
partial def pp (t : Term) (d : Nat) (ctx : Nat) (quoteStr : Bool) : PM String := do
  let st := (← get).store
  match st.deref t d with
  | .const c => cname c
  | .bound l => return s!"c{l}"
  | .lit (.int i) => return toString i
  | .lit (.float f) => return fmtFloat f
  | .lit (.str s) => return if quoteStr then "\"" ++ s ++ "\"" else s
  | .builtinData o => return s!"<{o.typeName}#{o.handle}>"
  | .cvar i _ => return s!"_C{i}"
  | .uvar u args =>
    let n ← varName u
    ppApp n args d ctx quoteStr
  | .lam b =>
    let body ← pp b (d + 1) 0 quoteStr
    let s := s!"c{d} \\ {body}"
    return if ctx > 0 then "(" ++ s ++ ")" else s
  | .app h args =>
    match h with
    | .const c =>
      let n ← cname c
      if c == cCons && args.size == 2 then ppList t d quoteStr
      else
        match opInfo n with
        | some (prec, lc, rc) =>
          if args.size == 2 then
            let a ← pp args[0]! d lc quoteStr
            let b ← pp args[1]! d rc quoteStr
            let s := s!"{a} {n} {b}"
            return if prec < ctx then "(" ++ s ++ ")" else s
          else ppApp n args d ctx quoteStr
        | none => ppApp n args d ctx quoteStr
    | _ =>
      let hs ← pp h d 1000 quoteStr
      ppApp hs args d ctx quoteStr

partial def ppApp (h : String) (args : Array Term) (d ctx : Nat) (q : Bool) : PM String := do
  if args.isEmpty then return h
  let mut parts : Array String := #[h]
  for i in [0:args.size] do
    let a := args[i]!
    let lastLam :=
      i + 1 == args.size && (match (← get).store.deref a d with | .lam _ => true | _ => false)
    if lastLam then
      parts := parts.push (← pp a d 0 q)
    else parts := parts.push (← pp a d 1000 q)
  let s := " ".intercalate parts.toList
  return if ctx ≥ 1000 then "(" ++ s ++ ")" else s

partial def ppList (t : Term) (d : Nat) (q : Bool) : PM String := do
  -- collect elements of a `::` chain
  let mut elems : Array String := #[]
  let mut cur := t
  let mut tail : Option String := none
  repeat
    match (← get).store.deref cur d with
    | .app (.const c) #[x, rest] =>
      if c == cCons then
        elems := elems.push (← pp x d 111 q)
        cur := rest
      else
        tail := some (← pp cur d 0 q); break
    | .const c =>
      if c == cNil then break
      else tail := some (← pp cur d 0 q); break
    | other =>
      tail := some (← pp other d 0 q); break
  let body := wrap elems
  match tail with
  | none => return "[" ++ body ++ "]"
  | some tl => return "[" ++ body ++ " | " ++ tl ++ "]"
where
  wrap (elems : Array String) : String := Id.run do
    -- OCaml Format-like wrapping at 80 columns: break after ", " when the next item
    -- would overflow, indenting by one column
    let mut out := ""
    let mut col := 1
    for i in [0:elems.size] do
      let e := elems[i]!
      if i > 0 then
        out := out ++ ", "; col := col + 2
        if col + e.length > 80 then
          out := out ++ "\n "; col := 1
      out := out ++ e; col := col + e.length
    return out
end

end Print


/-! ### Arithmetic and core builtins -/

namespace Builtins

/-- Evaluated arithmetic/string value; `term` is an unknown function application, which
`is` returns unevaluated (as the oracle does). -/
inductive Val where
  | int (i : Int)
  | float (f : Float)
  | str (s : String)
  | term (t : Term)

def Val.toTerm : Val → Term
  | .int i => .lit (.int i)
  | .float f => .lit (.float f)
  | .str s => .lit (.str s)
  | .term t => t

def floatStr (f : Float) : String := Print.fmtFloat f

partial def eval (c : BCtx) (t : Term) : Except String Val := do
  match c.store.deref t c.depth with
  | .lit (.int i) => return .int i
  | .lit (.float f) => return .float f
  | .lit (.str s) => return .str s
  | .uvar .. => throw "Evaluation of a non closed term. Maybe delay this predicate call and declare a constraint."
  | .app (.const op) args =>
    let name := c.syms.name op
    let vs ← args.mapM (eval c)
    apply name vs (.app (.const op) (vs.map Val.toTerm))
  | .const op =>
    let name := c.syms.name op
    apply name #[] (.const op)
  | t => return .term t
where
  apply (name : String) (vs : Array Val) (orig : Term) : Except String Val := do
    let bad : Except String Val := throw s!"Wrong arguments to {name}"
    match name, vs with
    | "+", #[.int a, .int b] | "i+", #[.int a, .int b] => return .int (a + b)
    | "-", #[.int a, .int b] | "i-", #[.int a, .int b] => return .int (a - b)
    | "*", #[.int a, .int b] | "i*", #[.int a, .int b] => return .int (a * b)
    | "div", #[.int a, .int b] =>
      if b == 0 then throw "Division by zero" else return .int (Int.tdiv a b)
    | "mod", #[.int a, .int b] =>
      if b == 0 then throw "Division by zero" else return .int (Int.tmod a b)
    | "abs", #[.int a] => return .int a.natAbs
    | "abs", #[.float a] => return .float (if a < 0 then -a else a)
    | "~", #[.int a] => return .int (-a)
    | "~", #[.float a] => return .float (-a)
    | "min", #[.int a, .int b] => return .int (min a b)
    | "max", #[.int a, .int b] => return .int (max a b)
    | "min", #[.float a, .float b] => return .float (if a < b then a else b)
    | "max", #[.float a, .float b] => return .float (if a < b then b else a)
    | "+", #[.float a, .float b] | "r+", #[.float a, .float b] => return .float (a + b)
    | "-", #[.float a, .float b] | "r-", #[.float a, .float b] => return .float (a - b)
    | "*", #[.float a, .float b] | "r*", #[.float a, .float b] => return .float (a * b)
    | "/", #[.float a, .float b] | "r/", #[.float a, .float b] => return .float (a / b)
    | "^", #[.str a, .str b] => return .str (a ++ b)
    | "sqrt", #[.float a] => return .float a.sqrt
    | "ln", #[.float a] => return .float (Float.log a)
    | "cos", #[.float a] => return .float (Float.cos a)
    | "sin", #[.float a] => return .float (Float.sin a)
    | "atan", #[.float a] => return .float (Float.atan a)
    | "int_to_real", #[.int a] => return .float (Float.ofInt a)
    | "truncate", #[.float a] => return .int (a.toInt64.toInt)
    | "floor", #[.float a] => return .int (a.floor.toInt64.toInt)
    | "ceil", #[.float a] => return .int (a.ceil.toInt64.toInt)
    | "size", #[.str a] => return .int a.length
    | "substring", #[.str a, .int i, .int l] =>
      if i < 0 || l < 0 || i + l > a.length then throw "substring: out of range"
      else return .str (String.ofList ((a.toList.drop i.toNat).take l.toNat))
    | "int_to_string", #[.int a] => return .str (toString a)
    | "string_to_int", #[.str a] =>
      match a.toInt? with | some i => return .int i | none => throw "string_to_int: not an integer"
    | "real_to_string", #[.float a] => return .str (floatStr a)
    | "+", _ | "-", _ | "*", _ | "/", _ | "div", _ | "mod", _ | "i+", _ | "r+", _
    | "i-", _ | "r-", _ | "i*", _ | "r*", _ | "r/", _ | "^", _ | "abs", _ | "~", _
    | "sqrt", _ | "ln", _ | "cos", _ | "sin", _ | "atan", _ | "truncate", _ | "floor", _
    | "ceil", _ | "int_to_real", _ | "size", _ | "substring", _ | "int_to_string", _
    | "string_to_int", _ | "real_to_string", _ | "min", _ | "max", _ =>
      -- the constant is a known function but the operands do not fit
      if vs.any (fun | .term _ => true | _ => false) then return .term orig else bad
    | _, _ => return .term orig

def cmpVals (a b : Val) : Option Ordering :=
  match a, b with
  | .int x, .int y => some (compare x y)
  | .str x, .str y => some (compare x y)
  | .float x, .float y => some (if x < y then .lt else if x == y then .eq else .gt)
  | _, _ => none

def one (c : BCtx) (args : Array Term) : BResult :=
  .alts c.store (.cons args (Thunk.mk fun _ => .nil))

def sig (name : String) (modes : List Mode) : BuiltinSig :=
  { name, modes := modes.toArray, type := .con "any" [] }

/-- Minimal backtracking regular-expression matcher (literals, `.`, classes, `* + ?`,
alternation, grouping, anchors) used by `rex_match`. -/
inductive Rx where
  | chr (c : Char) | any | cls (neg : Bool) (items : List (Char × Char))
  | seq (a b : Rx) | alt (a b : Rx) | star (a : Rx) | plus (a : Rx) | opt (a : Rx) | eps
  | bol | eol
  deriving Inhabited

mutual
partial def rxAlt (cs : Array Char) (i : Nat) : Rx × Nat :=
  let (a, i) := rxSeq cs i
  if i < cs.size && cs[i]! == '|' then
    let (b, j) := rxAlt cs (i + 1)
    (.alt a b, j)
  else (a, i)

partial def rxSeq (cs : Array Char) (i : Nat) : Rx × Nat := Id.run do
  let mut r := Rx.eps
  let mut i := i
  while i < cs.size && cs[i]! != '|' && cs[i]! != ')' do
    let (a, j) := rxAtom cs i
    i := j
    let mut a := a
    while i < cs.size && (cs[i]! == '*' || cs[i]! == '+' || cs[i]! == '?') do
      a := match cs[i]! with | '*' => .star a | '+' => .plus a | _ => .opt a
      i := i + 1
    r := .seq r a
  return (r, i)

partial def rxAtom (cs : Array Char) (i : Nat) : Rx × Nat :=
  match cs[i]! with
  | '.' => (.any, i + 1)
  | '^' => (.bol, i + 1)
  | '$' => (.eol, i + 1)
  | '(' =>
    let (r, j) := rxAlt cs (i + 1)
    (r, j + 1)
  | '\\' => if i + 1 < cs.size then (.chr cs[i+1]!, i + 2) else (.chr '\\', i + 1)
  | '[' => Id.run do
    let mut j := i + 1
    let neg := j < cs.size && cs[j]! == '^'
    if neg then j := j + 1
    let mut items : List (Char × Char) := []
    while j < cs.size && cs[j]! != ']' do
      if j + 2 < cs.size && cs[j+1]! == '-' && cs[j+2]! != ']' then
        items := (cs[j]!, cs[j+2]!) :: items; j := j + 3
      else
        items := (cs[j]!, cs[j]!) :: items; j := j + 1
    return (.cls neg items, j + 1)
  | c => (.chr c, i + 1)
end

def parseRx (cs : Array Char) (i : Nat) : Rx × Nat := rxAlt cs i

/-- Continuation-passing matcher: `m r s i k` matches `r` at position `i` of `s`. -/
partial def rxMatch (r : Rx) (s : Array Char) (i : Nat) (k : Nat → Bool) : Bool :=
  match r with
  | .eps => k i
  | .chr c => i < s.size && s[i]! == c && k (i + 1)
  | .any => i < s.size && k (i + 1)
  | .cls neg items =>
    i < s.size &&
      (items.any (fun (lo, hi) => lo ≤ s[i]! && s[i]! ≤ hi) != neg) && k (i + 1)
  | .seq a b => rxMatch a s i (fun j => rxMatch b s j k)
  | .alt a b => rxMatch a s i k || rxMatch b s i k
  | .opt a => rxMatch a s i k || k i
  | .star a => rxMatch a s i (fun j => j > i && rxMatch (.star a) s j k) || k i
  | .plus a => rxMatch a s i (fun j => rxMatch (.star a) s j k)
  | .bol => i == 0 && k i
  | .eol => i == s.size && k i

def rexMatch (pat str : String) : Bool :=
  let (r, _) := parseRx pat.toList.toArray 0
  rxMatch r str.toList.toArray 0 (fun j => j == str.length)

/-- The core builtin table. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Core builtins]]
def core (m : Type → Type) [Monad m] [Output m] : List (Builtin m) :=
  let pure' (b : BResult) : m BResult := pure b
  let cmp (name : String) (ok : Ordering → Bool) : Builtin m :=
    { sig := sig name [.i, .i]
      run := fun c args => pure' <|
        match eval c args[0]!, eval c args[1]! with
        | .ok a, .ok b =>
          match cmpVals a b with
          | some o => if ok o then one c args else .fail
          | none => .error s!"Wrong arguments to {name}"
        | .error e, _ | _, .error e => .error e }
  let strOf (c : BCtx) (t : Term) : Option String :=
    match c.store.deref t c.depth with | .lit (.str s) => some s | _ => none
  let intOf (c : BCtx) (t : Term) : Option Int :=
    match c.store.deref t c.depth with | .lit (.int i) => some i | _ => none
  [ { sig := sig "is" [.o, .i]
      run := fun c args => pure' <|
        match eval c args[1]! with
        | .ok v => one c #[v.toTerm, args[1]!]
        | .error e => .error e },
    cmp "<" (· == .lt), cmp ">" (· == .gt), cmp "=<" (· != .gt), cmp ">=" (· != .lt),
    cmp "i<" (· == .lt), cmp "i>" (· == .gt), cmp "i=<" (· != .gt), cmp "i>=" (· != .lt),
    cmp "r<" (· == .lt), cmp "r>" (· == .gt), cmp "r=<" (· != .gt), cmp "r>=" (· != .lt),
    cmp "s<" (· == .lt), cmp "s>" (· == .gt), cmp "s=<" (· != .gt), cmp "s>=" (· != .lt),
    { sig := sig "==" [.i, .i]
      run := fun c args => pure' <|
        if c.store.zonk args[0]! c.depth == c.store.zonk args[1]! c.depth
        then one c args else .fail },
    { sig := sig "print" []
      run := fun c args => do
        let ps : Print.PS := { syms := c.syms, store := c.store }
        let (strs, ps') := (args.mapM fun a => Print.pp a c.depth 0 false).run ps
        Output.write (" ".intercalate strs.toList ++ "\n")
        return .alts ps'.store (.cons args (Thunk.mk fun _ => .nil)) },
    { sig := sig "term_to_string" [.i, .o]
      run := fun c args => pure' <|
        let ps : Print.PS := { syms := c.syms, store := c.store }
        let (s, ps') := (Print.pp args[0]! c.depth 0 true).run ps
        .alts ps'.store (.cons #[args[0]!, .lit (.str s)] (Thunk.mk fun _ => .nil)) },
    { sig := sig "halt" []
      run := fun _ _ => pure' (.error "halt") },
    { sig := sig "rex_match" [.i, .i]
      run := fun c args => pure' <|
        match strOf c args[0]!, strOf c args[1]! with
        | some p, some s => if rexMatch p s then one c args else .fail
        | _, _ => .error "rex_match: strings expected" },
    { sig := sig "rex.match" [.i, .i]
      run := fun c args => pure' <|
        match strOf c args[0]!, strOf c args[1]! with
        | some p, some s => if rexMatch p s then one c args else .fail
        | _, _ => .error "rex.match: strings expected" },
    { sig := sig "var" [.i]
      run := fun c args => pure' <|
        match c.store.deref args[0]! c.depth with
        | .uvar .. => one c args
        | _ => .fail },
    { sig := sig "name" [.i]
      run := fun c args => pure' <|
        match c.store.deref args[0]! c.depth with
        | .bound _ => one c args
        | _ => .fail } ]

end Builtins

end Elpi
