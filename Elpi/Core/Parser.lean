import Std.Data.HashSet
import Std.Data.HashMap

/-!
# Parser

Hand-written lexer and Pratt parser for the ELPI 1.18 surface syntax over its fixed
operator table, producing a positioned AST; plus spilling elimination and the loader
that resolves `accumulate` and `namespace`.

The operator table was determined black-box against the oracle (`elpi -parse-term`).
-/

-- @lat: [[components#Parser]]

namespace Elpi

structure Pos where
  file : String := ""
  line : Nat := 1
  col : Nat := 0
  deriving BEq, Repr, Inhabited

def Pos.toString (p : Pos) : String := s!"{p.file}:{p.line}:{p.col}"

/-- Surface terms. Lists are `::`/`[]` applications. -/
inductive STm where
  | const (n : String) (p : Pos)
  | var (n : String) (p : Pos)
  | int (i : Int) (p : Pos)
  | float (f : Float) (p : Pos)
  | str (s : String) (p : Pos)
  | app (f : STm) (args : List STm) (p : Pos)
  | lam (x : String) (b : STm) (p : Pos)
  | spill (g : STm) (p : Pos)
  deriving Inhabited

def STm.pos : STm → Pos
  | .const _ p | .var _ p | .int _ p | .float _ p | .str _ p
  | .app _ _ p | .lam _ _ p | .spill _ p => p

/-- Surface types. -/
inductive STy where
  | con (n : String) (args : List STy) (p : Pos)
  | var (n : String) (p : Pos)
  | arrow (a b : STy) (p : Pos)
  deriving Inhabited

inductive Mode | i | o
  deriving BEq, Repr, Inhabited

structure Attrs where
  name : Option String := none
  before : Option String := none
  after : Option String := none
  deriving Inhabited

inductive Decl where
  | kind (names : List String) (ty : STy) (p : Pos)
  | type (names : List String) (ty : STy) (p : Pos)
  | pred (name : String) (args : List (Mode × STy)) (p : Pos)
  | typeabbrev (name : String) (params : List String) (ty : STy) (p : Pos)
  | clause (attrs : Attrs) (t : STm) (p : Pos)
  | accumulate (file : String) (p : Pos)
  | ns (n : String) (ds : List Decl) (p : Pos)
  deriving Inhabited

structure ParseError where
  pos : Pos
  msg : String
  deriving Inhabited

def ParseError.toString (e : ParseError) : String := s!"{e.pos.toString}: {e.msg}"

namespace Parser

inductive Tok where
  | ident (s : String)        -- lowercase / symbolic-ident constant
  | var (s : String)
  | int (i : Int)
  | float (f : Float)
  | str (s : String)
  | sym (s : String)          -- operator symbols such as `:-`, `=>`, `::`
  | bind (s : String)         -- `x\`
  | lp | rp | lb | rb | lc | rc
  | comma | semi | bar | dot
  | eof
  deriving BEq, Inhabited

structure Token where
  tok : Tok
  pos : Pos
  /-- Whitespace immediately before the token. -/
  space : Bool
  deriving Inhabited

def isIdStart (c : Char) : Bool := c.isLower
def isVarStart (c : Char) : Bool := c.isUpper || c == '_'
def isIdChar (c : Char) : Bool :=
  c.isAlphanum || "_'-+*/^<>=~?@#&!$".contains c
def isSymChar (c : Char) : Bool := "=<>~+-*/^?@#&$:!".contains c

/-- Tokenise a source text. -/
partial def lex (file : String) (src : String) : Except ParseError (Array Token) := do
  let cs := src.toList.toArray
  let n := cs.size
  let mut out : Array Token := #[]
  let mut i := 0
  let mut line := 1
  let mut col := 0
  let mut space := true
  let adv (c : Char) (line col : Nat) : Nat × Nat :=
    if c == '\n' then (line + 1, 0) else (line, col + 1)
  while i < n do
    let c := cs[i]!
    let pos : Pos := { file, line, col }
    if c.isWhitespace then
      (line, col) := adv c line col; i := i + 1; space := true
    else if c == '%' then
      while i < n && cs[i]! != '\n' do i := i + 1; col := col + 1
      space := true
    else if c == '/' && i + 1 < n && cs[i+1]! == '*' then
      i := i + 2; col := col + 2
      let mut closed := false
      while i < n && !closed do
        if cs[i]! == '*' && i + 1 < n && cs[i+1]! == '/' then
          closed := true; i := i + 2; col := col + 2
        else
          (line, col) := adv cs[i]! line col; i := i + 1
      if !closed then throw { pos, msg := "unterminated comment" }
      space := true
    else
      let mut tok : Tok := .eof
      let mut len := 1
      if c == '"' then
        let mut j := i + 1
        let mut s := ""
        let mut closed := false
        while j < n && !closed do
          let d := cs[j]!
          if d == '"' then closed := true; j := j + 1
          else if d == '\\' && j + 1 < n then
            let e := cs[j+1]!
            s := s.push (if e == 'n' then '\n' else if e == 't' then '\t' else e)
            j := j + 2
          else s := s.push d; j := j + 1
        if !closed then throw { pos, msg := "unterminated string" }
        tok := .str s
        -- keep line/col roughly right for multi-line strings
        for k in [i:j] do
          (line, col) := adv cs[k]! line col
        out := out.push { tok, pos, space }
        i := j; space := false
        continue
      else if c.isDigit then
        let mut j := i
        while j < n && cs[j]!.isDigit do j := j + 1
        let isFloat := j + 1 < n && cs[j]! == '.' && cs[j+1]!.isDigit
        if isFloat then
          j := j + 1
          while j < n && cs[j]!.isDigit do j := j + 1
          tok := .float (floatOf (String.ofList (cs.extract i j).toList))
        else
          tok := .int (String.ofList (cs.extract i j).toList).toInt!
        len := j - i
      else if isVarStart c then
        let mut j := i + 1
        while j < n && (isIdChar cs[j]! || (cs[j]! == '.' && j + 1 < n && cs[j+1]!.isAlphanum)) do
          j := j + 1
        let s := String.ofList (cs.extract i j).toList
        len := j - i
        if j < n && cs[j]! == '\\' then
          tok := .bind s; len := len + 1
        else tok := .var s
      else if isIdStart c then
        let mut j := i + 1
        while j < n && (isIdChar cs[j]! || (cs[j]! == '.' && j + 1 < n && cs[j+1]!.isAlphanum)) do
          j := j + 1
        let s := String.ofList (cs.extract i j).toList
        len := j - i
        if j < n && cs[j]! == '\\' then
          tok := .bind s; len := len + 1
        else tok := .ident s
      else if c == '(' then tok := .lp
      else if c == ')' then tok := .rp
      else if c == '[' then tok := .lb
      else if c == ']' then tok := .rb
      else if c == '{' then tok := .lc
      else if c == '}' then tok := .rc
      else if c == ',' then tok := .comma
      else if c == ';' then tok := .semi
      else if c == '|' then tok := .bar
      else if c == '.' then tok := .dot
      else if isSymChar c then
        let mut j := i + 1
        while j < n && isSymChar cs[j]! do j := j + 1
        -- `-` directly followed by a digit after whitespace is a negative literal
        if c == '-' && j == i + 1 && j < n && cs[j]!.isDigit && space then
          let mut k := j
          while k < n && cs[k]!.isDigit do k := k + 1
          if k + 1 < n && cs[k]! == '.' && cs[k+1]!.isDigit then
            k := k + 1
            while k < n && cs[k]!.isDigit do k := k + 1
            tok := .float (floatOf (String.ofList (cs.extract i k).toList))
          else
            tok := .int (String.ofList (cs.extract i k).toList).toInt!
          len := k - i
        else
          tok := .sym (String.ofList (cs.extract i j).toList)
          len := j - i
      else if c == '!' then tok := .sym "!"
      else if c == '\\' then tok := .sym "\\"
      else
        throw { pos, msg := s!"unexpected character '{c}'" }
      out := out.push { tok, pos, space }
      col := col + len; i := i + len; space := false
  out := out.push { tok := .eof, pos := { file, line, col }, space }
  return out
where
  floatOf (s : String) : Float :=
    match s.splitOn "." with
    | [a, b] =>
      Float.ofScientific (a ++ b).toNat! true b.length
    | _ => 0.0

/-- Binary operator table: precedence, left bound, right bound (non-associative operators
use the same bound on both sides plus one). -/
def infixInfo (s : String) : Option (Nat × Nat × Nat) :=
  let l (p : Nat) := some (p, p, p + 1)
  let r (p : Nat) := some (p, p + 1, p)
  let n (p : Nat) := some (p, p + 1, p + 1)
  match s with
  | ":-" | "?-" => n 1
  | ";" => r 100
  | "," | "&" => r 110
  | "->" => r 120
  | "=>" => r 129
  | "=" | "==" | "<" | ">" | "=<" | ">=" | "is" | "<=" | "<-" | "r<" | "r>" | "r=<" | "r>="
  | "i<" | "i>" | "i=<" | "i>=" | "s<" | "s>" | "s=<" | "s>=" | "=!=" | "~=" => n 130
  | "::" => r 140
  | "+" | "-" | "^" | "r+" | "r-" | "i+" | "i-" => l 150
  | "*" | "/" | "div" | "mod" | "rdiv" | "r*" | "i*" | "**" | "r/" | "i/" => l 160
  | _ => none

structure PState where
  toks : Array Token
  i : Nat := 0

abbrev PM := StateT PState (Except ParseError)

def peek : PM Token := do
  let s ← get
  return s.toks[s.i]!

def peekAt (k : Nat) : PM Token := do
  let s ← get
  return s.toks[min (s.i + k) (s.toks.size - 1)]!

def advance : PM Unit := modify fun s => { s with i := min (s.i + 1) (s.toks.size - 1) }

def fail {α : Type} (p : Pos) (msg : String) : PM α := throw { pos := p, msg }

def tokDesc : Tok → String
  | .ident s | .var s | .sym s | .bind s => s
  | .int i => toString i
  | .float f => toString f
  | .str s => s!"\"{s}\""
  | .lp => "(" | .rp => ")" | .lb => "[" | .rb => "]" | .lc => "{" | .rc => "}"
  | .comma => "," | .semi => ";" | .bar => "|" | .dot => "." | .eof => "end of input"

def expect (t : Tok) : PM Unit := do
  let k ← peek
  if k.tok == t then advance
  else fail k.pos s!"expected '{tokDesc t}' but found '{tokDesc k.tok}'"

/-- The operator name carried by a token, if the token can be an infix operator. -/
def opOf : Tok → Option String
  | .sym s => if (infixInfo s).isSome then some s else none
  | .ident s => if (infixInfo s).isSome then some s else none
  | .comma => some ","
  | .semi => some ";"
  | _ => none

/-- Can this token start an application argument? -/
def startsArg : Tok → Bool
  | .ident s => (infixInfo s).isNone
  | .var _ | .int _ | .float _ | .str _ | .bind _ | .lp | .lb | .lc => true
  | .sym "!" => true
  | _ => false

mutual
partial def parseExpr (minPrec : Nat) : PM STm := do
  let lhs ← parseApp
  parseInfix minPrec lhs

partial def parseInfix (minPrec : Nat) (lhs : STm) : PM STm := do
  let t ← peek
  match opOf t.tok with
  | none => return lhs
  | some op =>
    match infixInfo op with
    | none => return lhs
    | some (prec, _, rb) =>
      if prec < minPrec then return lhs
      advance
      let rhs ← parseExpr rb
      let name := if op == "&" then "," else op
      let node := STm.app (.const name t.pos) [lhs, rhs] t.pos
      -- non-associative operators may not chain
      parseInfix minPrec node

partial def parseApp : PM STm := do
  let h ← parseAtom
  let mut args : Array STm := #[]
  repeat
    let t ← peek
    if startsArg t.tok then
      -- `x\ body` already extends as far as possible
      args := args.push (← parseAtom)
    else break
  if args.isEmpty then return h
  else return .app h args.toList h.pos

partial def parseAtom : PM STm := do
  let t ← peek
  match t.tok with
  | .ident s => advance; return .const s t.pos
  | .var s => advance; return .var s t.pos
  | .int i => advance; return .int i t.pos
  | .float f => advance; return .float f t.pos
  | .str s => advance; return .str s t.pos
  | .sym "!" => advance; return .const "!" t.pos
  | .bind x =>
    advance
    let b ← parseExpr 0
    return .lam x b t.pos
  | .lp =>
    advance
    let n ← peek
    -- parenthesised operator, e.g. `(=>)`
    match n.tok with
    | .sym s | .ident s =>
      let n2 ← peekAt 1
      if n2.tok == .rp && (infixInfo s).isSome then
        advance; advance; return .const s n.pos
      else
        let e ← parseExpr 0
        expect .rp; return e
    | .comma =>
      let n2 ← peekAt 1
      if n2.tok == .rp then advance; advance; return .const "," n.pos
      else fail n.pos "unexpected ','"
    | _ =>
      let e ← parseExpr 0
      expect .rp
      return e
  | .lb =>
    advance
    let n ← peek
    if n.tok == .rb then advance; return .const "[]" t.pos
    let mut elems : Array STm := #[← parseExpr 111]
    let mut tail : STm := .const "[]" t.pos
    repeat
      let k ← peek
      if k.tok == .comma then advance; elems := elems.push (← parseExpr 111)
      else if k.tok == .bar then
        advance; tail ← parseExpr 111; expect .rb; break
      else expect .rb; break
    return elems.foldr (fun e acc => .app (.const "::" t.pos) [e, acc] t.pos) tail
  | .lc =>
    advance
    let g ← parseExpr 0
    expect .rc
    return .spill g t.pos
  | k => fail t.pos s!"term expected, found '{tokDesc k}'"
end

/-! ### Types -/

mutual
partial def parseType : PM STy := do
  let a ← parseBType
  let t ← peek
  if t.tok == .sym "->" then
    advance
    let b ← parseType
    return .arrow a b t.pos
  else return a

partial def parseBType : PM STy := do
  let t ← peek
  match t.tok with
  | .ident s =>
    advance
    let mut args : Array STy := #[]
    repeat
      let k ← peek
      match k.tok with
      | .ident _ | .var _ | .lp => args := args.push (← parseAType)
      | _ => break
    return .con s args.toList t.pos
  | _ => parseAType

partial def parseAType : PM STy := do
  let t ← peek
  match t.tok with
  | .ident s => advance; return .con s [] t.pos
  | .var s => advance; return .var s t.pos
  | .lp =>
    advance
    let ty ← parseType
    expect .rp
    return ty
  | k => fail t.pos s!"type expected, found '{tokDesc k}'"
end

/-! ### Declarations -/

def parseNameList : PM (List String) := do
  let mut names : Array String := #[]
  repeat
    let t ← peek
    match t.tok with
    | .ident s => advance; names := names.push s
    | .sym s => advance; names := names.push s
    | .lb =>
      advance; expect .rb; names := names.push "[]"
    | .lp =>
      advance
      let n ← peek
      match n.tok with
      | .sym s | .ident s => advance; expect .rp; names := names.push s
      | .comma => advance; expect .rp; names := names.push ","
      | .semi => advance; expect .rp; names := names.push ";"
      | _ => fail n.pos "operator name expected"
    | k => fail t.pos s!"constant name expected, found '{tokDesc k}'"
    let k ← peek
    if k.tok == .comma then advance else break
  return names.toList

def parseModeArg : PM (Mode × STy) := do
  let t ← peek
  let m ← match t.tok with
    | .ident "i" => advance; pure Mode.i
    | .ident "o" => advance; pure Mode.o
    | _ => pure Mode.o
  let k ← peek
  if k.tok == .sym ":" then advance
  parseType >>= fun ty => pure (m, ty)

mutual
partial def parseDecls (closing : Bool) : PM (List Decl) := do
  let mut ds : Array Decl := #[]
  repeat
    let t ← peek
    if t.tok == .eof then
      if closing then fail t.pos "unexpected end of input, '}' expected"
      break
    if closing && t.tok == .rc then break
    ds := ds.push (← parseDecl)
  return ds.toList

partial def parseDecl : PM Decl := do
  let t ← peek
  match t.tok with
  | .ident "kind" =>
    advance
    let names ← parseNameList
    let ty ← parseType
    expect .dot
    return .kind names ty t.pos
  | .ident "type" =>
    advance
    let names ← parseNameList
    let ty ← parseType
    expect .dot
    return .type names ty t.pos
  | .ident "pred" =>
    advance
    let n ← parseNameList
    let mut args : Array (Mode × STy) := #[]
    let k ← peek
    if k.tok != .dot then
      args := args.push (← parseModeArg)
      repeat
        let k ← peek
        if k.tok == .comma then advance; args := args.push (← parseModeArg) else break
    expect .dot
    return .pred n.head! args.toList t.pos
  | .ident "typeabbrev" =>
    advance
    let k ← peek
    let (name, params) ← match k.tok with
      | .ident s => advance; pure (s, ([] : List String))
      | .lp =>
        advance
        let nm ← peek
        let .ident s := nm.tok | fail nm.pos "abbreviation name expected"
        advance
        let mut ps : Array String := #[]
        repeat
          let p ← peek
          match p.tok with
          | .var v => advance; ps := ps.push v
          | _ => break
        expect .rp
        pure (s, ps.toList)
      | _ => fail k.pos "abbreviation name expected"
    let ty ← parseType
    expect .dot
    return .typeabbrev name params ty t.pos
  | .ident "accumulate" =>
    advance
    let k ← peek
    let f ← match k.tok with
      | .ident s | .str s => advance; pure s
      | _ => fail k.pos "file name expected after 'accumulate'"
    expect .dot
    return .accumulate f t.pos
  | .ident "namespace" =>
    advance
    let k ← peek
    let .ident name := k.tok | fail k.pos "namespace name expected"
    advance
    expect .lc
    let ds ← parseDecls true
    expect .rc
    -- the block is closed by `}` and not followed by a dot
    return .ns name ds t.pos
  | .ident "macro" | .ident "shorten" | .ident "external" | .ident "constraint"
  | .ident "chr" | .ident "mode" =>
    fail t.pos s!"'{tokDesc t.tok}' is unsupported in this milestone"
  | _ =>
    let mut attrs : Attrs := {}
    repeat
      let a ← peek
      match a.tok with
      | .sym ":" =>
        let n ← peekAt 1
        match n.tok with
        | .ident "name" =>
          advance; advance
          let s ← peek
          let .str v := s.tok | fail s.pos "string expected after ':name'"
          advance; attrs := { attrs with name := some v }
        | .ident "before" =>
          advance; advance
          let s ← peek
          let .str v := s.tok | fail s.pos "string expected after ':before'"
          advance; attrs := { attrs with before := some v }
        | .ident "after" =>
          advance; advance
          let s ← peek
          let .str v := s.tok | fail s.pos "string expected after ':after'"
          advance; attrs := { attrs with after := some v }
        | .ident "index" =>
          -- ignored with a warning: first-argument indexing is kept
          advance; advance
          let l ← peek
          if l.tok == .lp then
            let mut depth := 0
            repeat
              let x ← peek
              if x.tok == .lp then depth := depth + 1
              if x.tok == .rp then depth := depth - 1
              if x.tok == .eof then fail x.pos "unterminated ':index'"
              advance
              if depth == 0 then break
        | .ident _ => advance; advance
        | _ => break
      | _ => break
    let c ← parseExpr 0
    expect .dot
    return .clause attrs c t.pos
end

def parseProgram (file src : String) : Except ParseError (List Decl) := do
  let toks ← lex file src
  let (ds, _) ← (parseDecls false).run { toks }
  return ds

/-- Parse a single query term (no trailing dot required). -/
def parseQuery (file src : String) : Except ParseError STm := do
  let toks ← lex file src
  let (t, st) ← (do let t ← parseExpr 0
                    let k ← peek
                    if k.tok == .dot then advance
                    pure t : PM STm).run { toks }
  let k := st.toks[st.i]!
  if k.tok != .eof then throw { pos := k.pos, msg := s!"unexpected '{tokDesc k.tok}'" }
  return t


end Parser

/-! ### Spilling -/

mutual
/-- Replace every `{G}` in an atomic goal by a fresh variable and collect the calls
`G V` in left-to-right order (inner spills first). -/
partial def extractSpills (t : STm) : StateM (Nat × Array STm × Array String) STm := do
  match t with
  | .spill g p =>
    let g' ← extractSpills g
    let (n, gs, vs) ← get
    let v := s!"%spill{n}"
    let call : STm :=
      match g' with
      | .app f as q => .app f (as ++ [.const v p]) q
      | f => .app f [.const v p] p
    set (n + 1, gs.push call, vs.push v)
    return .const v p
  | .app f args p =>
    let f' ← extractSpills f
    let args' ← args.mapM extractSpills
    return .app f' args' p
  | .lam x b p => return .lam x (← extractSpills b) p
  | t => return t
end

mutual
/-- Rewrite spilling in a goal: `p {q X}` becomes `sigma V\ (q X V, p V)`. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Spilling]]
partial def elimGoal (g : STm) (ctr : Nat) : STm × Nat :=
  match g with
  | .app (.const c cp) [a, b] p =>
    if c == "," || c == ";" || c == "->" then
      let (a', n1) := elimGoal a ctr
      let (b', n2) := elimGoal b n1
      (.app (.const c cp) [a', b'] p, n2)
    else if c == "=>" then
      let (d', n1) := elimClause a ctr
      let (b', n2) := elimGoal b n1
      (.app (.const c cp) [d', b'] p, n2)
    else atomic g ctr
  | .app (.const c cp) [.lam x b lp] p =>
    if c == "pi" || c == "sigma" then
      let (b', n) := elimGoal b ctr
      (.app (.const c cp) [.lam x b' lp] p, n)
    else atomic g ctr
  | .app (.const "not" cp) [a] p =>
    let (a', n) := elimGoal a ctr
    (.app (.const "not" cp) [a'] p, n)
  | _ => atomic g ctr
where
  atomic (g : STm) (ctr : Nat) : STm × Nat :=
    let (g', (n, calls, vars)) := (extractSpills g).run (ctr, #[], #[])
    if calls.isEmpty then (g, ctr)
    else
      -- calls were collected with arguments already spilled-free except nested ones,
      -- which `extractSpills` has already hoisted
      let body := calls.foldr (fun c acc => .app (.const "," g.pos) [c, acc] g.pos) g'
      let wrapped := vars.foldr (fun v acc =>
        .app (.const "sigma" g.pos) [.lam v acc g.pos] g.pos) body
      (wrapped, n)

/-- Spilling elimination for a clause (or hypothetical clause) term. -/
partial def elimClause (c : STm) (ctr : Nat) : STm × Nat :=
  match c with
  | .app (.const ":-" cp) [h, b] p =>
    let (b', n) := elimGoal b ctr
    (.app (.const ":-" cp) [h, b'] p, n)
  | .app (.const "pi" cp) [.lam x b lp] p =>
    let (b', n) := elimClause b ctr
    (.app (.const "pi" cp) [.lam x b' lp] p, n)
  | _ => (c, ctr)

end

def elimSpilling (c : STm) : STm := (elimClause c 0).1

/-- First occurrence of the constant `name` in a term. -/
partial def findConst (name : String) : STm → Option Pos
  | .const n p => if n == name then some p else none
  | .app f as _ => (findConst name f).orElse fun _ => as.findSome? (findConst name)
  | .lam _ b _ => findConst name b
  | .spill g _ => findConst name g
  | _ => none

/-- Features of later milestones are rejected at load time. -/
def unsupportedFeature (t : STm) : Option (Pos × String) :=
  match findConst "declare_constraint" t with
  | some p => some (p, "declare_constraint")
  | none => none

/-! ### Loading units: accumulate and namespaces -/

/-- Names directly declared or defined by a block of declarations. -/
partial def declaredNames (ds : List Decl) : Std.HashSet String :=
  ds.foldl (fun acc d =>
    match d with
    | .kind ns _ _ | .type ns _ _ => ns.foldl (·.insert ·) acc
    | .pred n _ _ => acc.insert n
    | .typeabbrev n _ _ _ => acc.insert n
    | .clause _ t _ =>
      let rec head : STm → Option String
        | .app (.const ":-" _) [h, _] _ => head h
        | .app (.const "," _) (h :: _) _ => head h
        | .app (.const n _) _ _ => some n
        | .const n _ => some n
        | _ => none
      match head t with | some n => acc.insert n | none => acc
    | _ => acc) {}

abbrev Scopes := List (String × Std.HashSet String)

def resolveName (scopes : Scopes) (n : String) : String :=
  match scopes.find? (fun (_, names) => names.contains n) with
  | some (pre, _) => pre ++ "." ++ n
  | none => n

partial def qualTm (scopes : Scopes) (bound : List String) : STm → STm
  | .const n p => if bound.contains n then .const n p else .const (resolveName scopes n) p
  | .var n p => .var n p
  | .app f as p => .app (qualTm scopes bound f) (as.map (qualTm scopes bound)) p
  | .lam x b p => .lam x (qualTm scopes (x :: bound) b) p
  | .spill g p => .spill (qualTm scopes bound g) p
  | t => t

partial def qualTy (scopes : Scopes) : STy → STy
  | .con n as p => .con (resolveName scopes n) (as.map (qualTy scopes)) p
  | .arrow a b p => .arrow (qualTy scopes a) (qualTy scopes b) p
  | t => t

/-- Flatten `namespace` blocks, prefixing declared names with `n.` and resolving short
names innermost-first. -/
partial def flattenNs (scopes : Scopes) (ds : List Decl) : List Decl :=
  ds.flatMap fun d =>
    let q (n : String) := if scopes.isEmpty then n else resolveName scopes n
    match d with
    | .ns n inner _ =>
      let full := match scopes with | [] => n | (pre, _) :: _ => pre ++ "." ++ n
      flattenNs ((full, declaredNames inner) :: scopes) inner
    | .kind ns ty p => [.kind (ns.map q) ty p]
    | .type ns ty p => [.type (ns.map q) (qualTy scopes ty) p]
    | .pred n args p => [.pred (q n) (args.map fun (m, t) => (m, qualTy scopes t)) p]
    | .typeabbrev n ps ty p => [.typeabbrev (q n) ps (qualTy scopes ty) p]
    | .clause a t p => [.clause a (qualTm scopes [] t) p]
    | d => [d]

/-- Resolve `accumulate` through `find` (file name, requesting file ↦ canonical path and
source), loading each unit at most once, and flatten namespaces. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Accumulate and namespaces]]
partial def loadUnits {m : Type → Type} [Monad m]
    (find : String → String → m (Option (String × String)))
    (file src : String) : m (Except ParseError (List Decl)) := do
  let rec go (file src : String) (seen : Std.HashSet String) :
      m (Except ParseError (List Decl × Std.HashSet String)) := do
    match Parser.parseProgram file src with
    | .error e => return .error e
    | .ok ds =>
      let rec expand (ds : List Decl) (seen : Std.HashSet String) :
          m (Except ParseError (List Decl × Std.HashSet String)) := do
        let mut out : Array Decl := #[]
        let mut seen := seen
        for d in ds do
          match d with
          | .accumulate f p =>
            match ← find f file with
            | none => return .error { pos := p, msg := s!"cannot find accumulated file '{f}'" }
            | some (canon, text) =>
              if seen.contains canon then pure ()
              else
                match ← go canon text (seen.insert canon) with
                | .error e => return .error e
                | .ok (inner, seen') =>
                  out := out ++ inner.toArray
                  seen := seen'
          | .ns n inner p =>
            match ← expand inner seen with
            | .error e => return .error e
            | .ok (inner', seen') =>
              out := out.push (.ns n inner' p)
              seen := seen'
          | d => out := out.push d
        return .ok (out.toList, seen)
      expand ds seen
  match ← go file src (({} : Std.HashSet String).insert file) with
  | .error e => return .error e
  | .ok (ds, _) => return .ok (flattenNs [] ds)

end Elpi
