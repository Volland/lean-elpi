import Lean
import Elpi.Lean.Commands

/-!
# Rule DSL

`elpi_rules name where` writes ELPI rules in Lean source against Lean types: predicate
signatures `pred p : T1 → … → Prop` (types with `deriving Elpi`) and clauses in ELPI syntax.
Clauses are type checked when the command is elaborated, with Lean positions; the command
defines `name.compiled : Elpi.CompiledProgram` (no parsing at runtime) and a typed query
helper `name.p` per predicate.
-/

-- @lat: [[components#Rule DSL]]

namespace Elpi

/-- An argument of a typed query: a value, or an output variable to be solved for. -/
inductive Arg (α : Type) where
  | val (a : α)
  | out

/-- A query built from a predicate and typed arguments; `none` marks an output variable. -/
structure Query where
  pred : ConstId
  args : Array (Option Term)

def Arg.toTerm? {α : Type} [ToElpi α] : Arg α → Option Term
  | .val a => some (toElpi a)
  | .out => none

partial def solveQueryGo {α : Type} [FromBindings α] (env : Env Id) (syms : Symbols)
    (names : Array (String × UVarId)) (M : Machine Unit) : LazyList (Except ElpiError α) :=
  match Id.run (runLoop env M) with
  | .yield sol M' =>
    .cons (FromBindings.decode (mkSolution syms names sol).bindings)
      (Thunk.mk fun _ => solveQueryGo env syms names M')
  | .exhausted _ _ => .nil
  | .outOfFuel => .cons (.error .outOfFuel) (Thunk.mk fun _ => .nil)
  | .error e => .cons (.error e) (Thunk.mk fun _ => .nil)

/-- Run a typed query on a compiled program: the output variables are the answer variables
(`O0`, `O1`, …) and decode with `FromElpi`/`FromBindings`. -/
def solveQuery {α : Type} [FromBindings α] (p : CompiledProgram) (q : Query)
    (fuel : Nat := defaultFuel) : LazyList (Except ElpiError α) :=
  let outs := (q.args.foldl (fun (acc : List String) a => if a.isNone then acc ++ [s!"O{acc.length}"] else acc) [])
  let prep := p.prepareRaw outs (fuel := fuel) fun vs => Id.run do
    let mut k := 0
    let mut args : Array Term := #[]
    for a in q.args do
      match a with
      | some t => args := args.push t
      | none => args := args.push vs[k]!; k := k + 1
    return if args.isEmpty then .const q.pred else .app (.const q.pred) args
  solveQueryGo (p.env Id prep.syms) prep.syms prep.names prep.machine

end Elpi

namespace Elpi.Cmd

open _root_.Lean Elab Command

/-- Parser for the body of `elpi_rules`: every following line that is blank or indented. -/
def rulesBlockFn : Parser.ParserFn := fun c s =>
  let input := c.input
  let start := s.pos
  let n := input.utf8ByteSize
  let rec scan (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | f + 1 =>
      if i ≥ n then n
      else if String.Pos.Raw.get input (String.Pos.Raw.mk i) == '\n' then
        -- a newline followed by a non-blank, non-indented character ends the block
        if i + 1 ≥ n then n
        else
          let nx := String.Pos.Raw.get input (String.Pos.Raw.mk (i + 1))
          if nx.isWhitespace then scan (i + 1) f else i + 1
      else scan (i + 1) f
  let stop := scan start.byteIdx (n + 1)
  Parser.mkNodeToken `Elpi.Cmd.rulesBlock start true c (s.setPos (String.Pos.Raw.mk stop))

def rulesBlock : Parser.Parser := { fn := rulesBlockFn, info := Parser.mkAtomicInfo "rulesBlock" }

@[combinator_formatter rulesBlock] def rulesBlock.formatter : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer rulesBlock] def rulesBlock.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

syntax (name := elpiRules) "elpi_rules " ident &"where " rulesBlock : command

/-- ELPI type of a Lean type written in a `pred` signature. -/
partial def tyToElpi (derived : Array DeriveEntry) (t : String) : Except String String := do
  let t := t.trimAscii.toString
  if t.startsWith "(" && t.endsWith ")" then return ← tyToElpi derived ((t.drop 1).dropEnd 1).toString
  -- split into head and arguments at top level
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for ch in t.toList do
    if ch == '(' then depth := depth + 1; cur := cur.push ch
    else if ch == ')' then depth := depth - 1; cur := cur.push ch
    else if ch == ' ' && depth == 0 then
      if !cur.isEmpty then parts := parts.push cur
      cur := ""
    else cur := cur.push ch
  if !cur.isEmpty then parts := parts.push cur
  match parts.toList with
  | [h] =>
    match h with
    | "Nat" | "Int" => return "int"
    | "String" => return "string"
    | "Bool" => return "bool"
    | "Float" => return "float"
    | "Name" => return "name"
    | "Expr" => return "term"
    | "Level" => return "level"
    | _ =>
      match derived.find? fun e => e.leanName.toString == h || e.leanName.getString! == h with
      | some e => return e.kind
      | none => throw s!"the type {h} has no ELPI counterpart (add `deriving Elpi`)"
  | [c, a] =>
    let a' ← tyToElpi derived a
    if c == "List" || c == "Array" then return s!"(list {a'})"
    else if c == "Option" then return s!"(option {a'})"
    else throw s!"the type constructor {c} has no ELPI counterpart"
  | _ => throw s!"cannot translate the type {t}"

/-- A parsed signature `pred p : T1 → … → Prop`. -/
structure RuleSig where
  name : String
  argTys : List String

def parseSig (seg : String) : Except String RuleSig := do
  let body := (seg.trimAscii.toString.drop 5).toString   -- after "pred "
  match body.splitOn ":" with
  | n :: rest =>
    let ty := String.intercalate ":" rest
    let ty := ty.replace "->" "→"
    let ts := (ty.splitOn "→").map (·.trimAscii.toString)
    match ts.reverse with
    | "Prop" :: args => return { name := n.trimAscii.toString, argTys := args.reverse }
    | _ => throw s!"the signature of {n.trimAscii.toString} must end in Prop"
  | [] => throw "bad signature"

/-- Replace the signature lines by generated ELPI `pred` declarations, keeping the line
structure so that clause positions stay exact. -/
def transformRules (derived : Array DeriveEntry) (text : String) :
    Except String (String × List (RuleSig × List String)) := do
  let mut out : Array String := #[]
  let mut sigs : Array (RuleSig × List String) := #[]
  for line in text.splitOn "\n" do
    if line.trimAscii.toString.startsWith "pred " then
      let segs := line.splitOn ";"
      let mut gen : Array String := #[]
      let mut rest : Array String := #[]
      for seg in segs do
        if seg.trimAscii.toString.startsWith "pred " then
          let sg ← parseSig seg
          let tys ← sg.argTys.mapM (tyToElpi derived)
          gen := gen.push ("pred " ++ sg.name ++ " " ++ ", ".intercalate (tys.map ("o:" ++ ·)) ++ ".")
          sigs := sigs.push (sg, tys)
        else if !seg.trimAscii.toString.isEmpty then rest := rest.push seg
      out := out.push (" ".intercalate gen.toList ++ " " ++ ";".intercalate rest.toList)
    else out := out.push line
  return ("\n".intercalate out.toList, sigs.toList)

-- @tg: implements:: [[openspec:elpi-runtime-library#Typed rule DSL]]
@[command_elab elpiRules] def elabRules : CommandElab := fun stx => do
  let name := stx[1].getId
  let (text, base?) :=
    match stx[3].isLit? `Elpi.Cmd.rulesBlock with
    | some v => (v, stx[3].getPos?)
    | none => ("", none)
  let env ← getEnv
  let derived := derivedEntries env
  let o : Origin := { label := "lp%", base?, text }
  let (text', sigs) ← match transformRules derived text with
    | .ok r => pure r
    | .error m => throwErrorAt stx[3] "{m}"
  let o := { o with text := text', orig? := some text }
  let find (n from_ : String) : IO (Option (String × String)) := do
    match ← Libraries.resolve {} n from_ with
    | .ok r => return some r
    | .error _ => return none
  let ds ← match ← loadUnits (m := IO) find o.label text' with
    | .ok ds => pure ds
    | .error e => reportElpiError o stx[3] e.toString
  let ds ← match ← liftTermElabM (Quote.elabDecls ds) with
    | .ok ds => pure ds
    | .error (pos, m) => reportElpiError o stx[3] s!"{pos.toString}: {m}"
  let mut pre : List Decl := []
  for sg in derivedSignatures env do
    match Parser.parseProgram "<signature>" sg with
    | .ok d => pre := pre ++ d
    | .error e => throwErrorAt stx s!"{e.toString}"
  let p ← match baseProgram with
    | .ok b =>
      match b.addDecls (pre ++ ds) with
      | .ok p => pure p
      | .error e => reportElpiError o stx[3] (toString e)
    | .error e => throwErrorAt stx "{e}"
  elabElpiProgram ⟨stx[1]⟩ (.ok p) stx
  -- typed query helpers
  for (sg, _) in sigs do
    let params := String.intercalate " " ((sg.argTys.zipIdx.map fun (t, i) => s!"(a{i} : Elpi.Arg ({t}))"))
    let args := String.intercalate ", " (sg.argTys.zipIdx.map fun (_, i) => s!"Elpi.Arg.toTerm? a{i}")
    elabText s!"def {name}.{sg.name} {params} : Elpi.Query := ⟨⟨{symbolId sg.name}⟩, #[{args}]⟩\n"

end Elpi.Cmd
