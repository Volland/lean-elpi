import Lean
import Elpi.LF.Erase
import Elpi.Lean.Libraries
import Elpi.Lean.Builtins
import Elpi.Lean.Quote
import Elpi.Lean.Marshal
import Elpi.Solver.Registry

/-!
# Commands

`elpi_program` compiles an ELPI program at elaboration time and defines
`<name>.compiled : CompiledProgram`; `elpi_main` turns such a program into an executable
entry point. The compiled program is embedded as plain data (no parsing at runtime).
-/

-- @lat: [[components#Commands]]

namespace Elpi.Cmd

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Command

/-! ### Embedding terms and programs as `Expr` -/

def natE (n : Nat) : Expr := toExpr n

partial def litE : Literal → Expr
  | .int i => mkApp (mkConst ``Literal.int) (toExpr i)
  | .float f =>
    -- a float is rebuilt from its decimal rendering without any parsing of ELPI
    let (m, e) := floatParts f
    mkApp (mkConst ``Literal.float)
      (mkApp3 (mkConst ``Float.ofScientific) (toExpr m) (toExpr true) (toExpr e))
  | .str s => mkApp (mkConst ``Literal.str) (toExpr s)
where
  floatParts (f : Float) : Nat × Nat :=
    let scaled := (f.abs * 1000000.0).round
    (scaled.toUInt64.toNat, 6)

partial def termE : Term → Expr
  | .const c => mkApp (mkConst ``Term.const) (mkApp (mkConst ``ConstId.mk) (natE c.idx))
  | .bound l => mkApp (mkConst ``Term.bound) (natE l)
  | .app h as => mkApp2 (mkConst ``Term.app) (termE h) (arrE as)
  | .lam b => mkApp (mkConst ``Term.lam) (termE b)
  | .uvar u as => mkApp2 (mkConst ``Term.uvar) (mkApp (mkConst ``UVarId.mk) (natE u.idx)) (arrE as)
  | .cvar i as => mkApp2 (mkConst ``Term.cvar) (natE i) (arrE as)
  | .lit l => mkApp (mkConst ``Term.lit) (litE l)
  | .builtinData o =>
    mkApp (mkConst ``Term.builtinData)
      (mkApp2 (mkConst ``Opaque.mk) (natE o.handle) (toExpr o.typeName))
where
  arrE (as : Array Term) : Expr :=
    let tm := mkConst ``Term
    mkApp2 (mkConst ``List.toArray [Level.zero]) tm
      (as.toList.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) tm (termE a) acc)
        (mkApp (mkConst ``List.nil [Level.zero]) tm))

instance : ToExpr Term where
  toExpr := termE
  toTypeExpr := mkConst ``Term

partial def tyE : Ty → Expr
  | .con n as =>
    let ty := mkConst ``Ty
    mkApp2 (mkConst ``Ty.con) (toExpr n)
      (as.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty (tyE a) acc)
        (mkApp (mkConst ``List.nil [Level.zero]) ty))
  | .arrow a b => mkApp2 (mkConst ``Ty.arrow) (tyE a) (tyE b)
  | .mv i => mkApp (mkConst ``Ty.mv) (natE i)
  | .gen i => mkApp (mkConst ``Ty.gen) (natE i)

instance : ToExpr Ty where
  toExpr := tyE
  toTypeExpr := mkConst ``Ty

instance : ToExpr Mode where
  toExpr | .i => mkConst ``Mode.i | .o => mkConst ``Mode.o
  toTypeExpr := mkConst ``Mode

instance : ToExpr Pos where
  toExpr p := mkApp3 (mkConst ``Pos.mk) (toExpr p.file) (toExpr p.line) (toExpr p.col)
  toTypeExpr := mkConst ``Pos

/-- The data a compiled program is rebuilt from, without any parsing. -/
structure ProgramData where
  names : List String
  consts : List (String × Nat × Ty)
  modes : List (String × Array Mode)
  items : Array (Nat × Term × Term × Nat × Option String × Pos × Option String × Option String)

def ProgramData.ofProgram (p : CompiledProgram) : ProgramData :=
  { names := p.syms.userNames
    consts := p.sig.consts.toList.map fun (n, sc) => (n, sc.nvars, sc.ty)
    modes := p.sig.modes.toList
    items := p.items.map fun it =>
      (it.pred.idx, it.clause.head, it.clause.body, it.clause.nvars, it.clause.name?,
       it.clause.pos, it.before?, it.after?) }

def ProgramData.toProgram (d : ProgramData) : CompiledProgram :=
  let syms : Symbols :=
    d.names.foldl (fun sy n => (sy.intern n).2) Symbols.initial
  let sig : Signature :=
    { consts := d.consts.foldl (init := {}) fun m (n, k, ty) => m.insert n { nvars := k, ty }
      modes := d.modes.foldl (init := {}) fun m (n, ms) => m.insert n ms }
  let items := d.items.map fun (c, h, b, nv, nm, pos, bf, af) =>
    ({ pred := ⟨c⟩, clause := { head := h, body := b, nvars := nv, name? := nm, pos },
       before? := bf, after? := af } : ClauseItem)
  let lists := (graft items).toOption.getD {}
  let modes := sig.modes.fold (init := ({} : Std.HashMap Nat (Array Mode))) fun m n ms =>
    match syms.find? n with
    | some c => m.insert c.idx ms
    | none => m
  { syms, sig, items, db := Database.ofLists lists, modes }

instance : ToExpr ProgramData where
  toExpr d :=
    mkApp4 (mkConst ``ProgramData.mk) (toExpr d.names) (toExpr d.consts) (toExpr d.modes)
      (toExpr d.items)
  toTypeExpr := mkConst ``ProgramData

def dataE (d : ProgramData) : Expr := toExpr d

/-- Parser invocation counter (see `Elpi.parserCalls`), exposed for tests. -/
def parserCount : IO Nat := parserCalls.get

/-- Define `<name>.compiled` from a program text or file at elaboration time. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Compiled program constants]]
def elabElpiProgram (name : Ident) (prog : Except ElpiError CompiledProgram) (ref : Syntax) :
    CommandElabM Unit := do
  match prog with
  | .error e => throwErrorAt ref "{e}"
  | .ok p =>
    let declName := name.getId ++ `compiled
    let value := mkApp (mkConst ``ProgramData.toProgram) (dataE (ProgramData.ofProgram p))
    liftCoreM <| addAndCompile <| .defnDecl
      { name := declName, levelParams := [], type := mkConst ``CompiledProgram
        value, hints := .abbrev, safety := .safe }

syntax (name := elpiProgramStr) "elpi_program " ident str : command
syntax (name := elpiProgramFile) "elpi_program " ident " from " str : command

@[command_elab elpiProgramStr] def elabProgramStr : CommandElab := fun stx => do
  let src := stx[2].isStrLit?.getD ""
  elabElpiProgram ⟨stx[1]⟩ (Program.load src) stx[2]

@[command_elab elpiProgramFile] def elabProgramFile : CommandElab := fun stx => do
  let path := stx[3].isStrLit?.getD ""
  let r ← liftIO (Program.loadFile path)
  elabElpiProgram ⟨stx[1]⟩ r stx[3]

/-- `elpi_main prog` defines `main` running the predicate `main` of `prog.compiled`. -/
-- @tg: implements:: [[openspec:elpi-cli#Compiled program executables]]
syntax (name := elpiMainStx) "elpi_main " ident : command

@[command_elab elpiMainStx] def elabElpiMain : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let compiled := mkIdent (id.getId ++ `compiled)
  elabCommand (← `(def main (args : List String) : IO UInt32 := Elpi.runMain $compiled args))


end Elpi.Cmd

namespace Elpi

/-- A reference to a program or database declared with `elpi_program` / `elpi_db`. -/
structure ProgramRef where
  name : Lean.Name

end Elpi

namespace Elpi.Cmd

open _root_.Lean Elab Command Meta

/-! ### Programs and databases in the environment -/

/-- Entries of the ELPI environment extension, replayed in import order. -/
inductive ElpiEntry where
  | program (name : Name)
  | db (name : Name)
  /-- A unit of accumulated declarations (already parsed and with quotations elaborated). -/
  | unit (target : Name) (decls : List Decl)
  /-- `elpi_accumulate P db D`. -/
  | useDb (target : Name) (db : Name)
  | tactic (name : Name) (prog : Name)
  | command (name : Name) (prog : Name)

-- @tg: implements:: [[openspec:lean-integration#Program and database declarations]]
initialize elpiExt : SimplePersistentEnvExtension ElpiEntry (Array ElpiEntry) ←
  registerSimplePersistentEnvExtension
    { addEntryFn := fun es e => es.push e
      addImportedFn := fun as => as.foldl (init := #[]) fun acc a => acc ++ a }

def elpiEntries (env : Environment) : Array ElpiEntry := elpiExt.getState env

def isProgram (env : Environment) (n : Name) : Bool :=
  (elpiEntries env).any fun | .program m => m == n | _ => false
def isDb (env : Environment) (n : Name) : Bool :=
  (elpiEntries env).any fun | .db m => m == n | _ => false

/-- The declarations accumulated into `target`, databases spliced in at the point where they
were accumulated. -/
partial def targetDecls (env : Environment) (target : Name) (fuel : Nat := 16) : List Decl :=
  if fuel == 0 then [] else
  (elpiEntries env).toList.flatMap fun
    | .unit t ds => if t == target then ds else []
    | .useDb t d => if t == target then targetDecls env d (fuel - 1) else []
    | _ => []

/-- Assemble the program `target` of an environment: prelude, standard library, the derived
type declarations, the signatures of registered builtins and the accumulated units. Nothing is
parsed: units hold ready declarations. -/
def assemble (env : Environment) (target : Name) (extra : List Decl := []) :
    Except ElpiError CompiledProgram := do
  let sigs := Registry.signatures env ++ derivedSignatures env
  let mut pre : List Decl := []
  for sg in sigs do
    match Parser.parseProgram "<signature>" sg with
    | .ok ds => pre := pre ++ ds
    | .error e => throw (.parse e.toString)
  let base ← baseProgram
  let p ← base.addDecls (pre ++ targetDecls env target ++ extra)
  let bs ← match Registry.pureBuiltins env with
    | .ok bs => pure bs
    | .error e => throw (.load e)
  let mut p : CompiledProgram := { p with extra := bs ++ p.extra }
  for e in (Registry.entries env).filter (·.kind == .handler) do
    let h : ConstraintHandler ← match Registry.evalImpl env {} e.declName with
      | .ok h => pure h
      | .error m => throw (.load m)
    p ← p.withHandler e.name h
  for e in (Registry.entries env).filter (·.kind == .hook) do
    let h : UnifHook ← match Registry.evalImpl env {} e.declName with
      | .ok h => pure h
      | .error m => throw (.load m)
    p := p.withHook h
  return p

/-! ### Source positions -/

/-- Byte offset in `text` of the character at (`line`, `col`), both counted as by the lexer
(lines from 1, columns in characters). -/
def offsetOf (text : String) (line col : Nat) : Nat := Id.run do
  let mut l := 1
  let mut c := 0
  let mut off := 0
  for ch in text.toList do
    if l == line && c == col then return off
    if ch == '\n' then
      l := l + 1
      c := 0
    else c := c + 1
    off := off + ch.utf8Size
  return off

/-- Where a source's text sits in the Lean file (inline sources), if anywhere. -/
structure Origin where
  /-- Label used as the file of ELPI positions. -/
  label : String
  /-- Byte position of the text's first character in the Lean file. -/
  base? : Option String.Pos.Raw := none
  text : String
  /-- The text as written in the Lean file, when `text` is a line-preserving rewrite of it. -/
  orig? : Option String := none

/-- A syntax range to report an ELPI diagnostic at: the token at the position. -/
def refAt (o : Origin) (fallback : Syntax) (line col : Nat) : Syntax :=
  match o.base? with
  | none => fallback
  | some base =>
    let src := o.orig?.getD o.text
    let off := offsetOf src line col
    let tail := String.Pos.Raw.extract src (String.Pos.Raw.mk off) (String.Pos.Raw.mk src.utf8ByteSize)
    let w := (tail.toRawSubstring.takeWhile fun c => !(Char.isWhitespace c || "().,;[]{}".contains c)).toString
    let start : String.Pos.Raw := ⟨base.byteIdx + off⟩
    let stop : String.Pos.Raw := ⟨start.byteIdx + max 1 w.utf8ByteSize⟩
    Syntax.atom (.synthetic start stop) ""

/-- Split `label:line:col: message` lines of an ELPI error. -/
def parsePositioned (label : String) (msg : String) : List (Nat × Nat × String) :=
  msg.splitOn "\n" |>.filterMap fun l =>
    if l.startsWith (label ++ ":") then
      match (l.drop (label.length + 1)).toString.splitOn ":" with
      | ln :: cl :: rest => do
        let a ← ln.toNat?
        let b ← cl.toNat?
        pure (a, b, String.intercalate ":" rest |>.trimAscii.toString)
      | _ => none
    else none

/-- Report an ELPI error (a message with positions inside `o`) as Lean diagnostics. -/
def reportElpiError {α : Type} (o : Origin) (ref : Syntax) (msg : String) : CommandElabM α := do
  let ps := parsePositioned o.label msg
  match o.base?, ps with
  | some _, _ :: _ =>
    for (l, c, m) in ps do
      logErrorAt (refAt o ref l c) m
    throwAbortCommand
  | _, _ => throwErrorAt ref "{msg}"

/-! ### Accumulation -/

/-- Parse a source, resolve `accumulate`, elaborate quotations and typecheck the result as an
extension of `target`; returns the ready declarations. -/
def processSource (target : Name) (o : Origin) (ref : Syntax) (leanFile : String) :
    CommandElabM (List Decl) := do
  let cfg : Libraries.Config := {}
  let find (name from_ : String) : IO (Option (String × String)) := do
    match ← Libraries.resolve cfg name from_ with
    | .ok r => return some r
    | .error _ => return none
  let ds ← match ← loadUnits (m := IO) find o.label o.text (pre := Elpi.LF.preprocessUnit) with
    | .ok ds => pure ds
    | .error e => reportElpiError o ref e.toString
  let ds ← match ← liftTermElabM (Quote.elabDecls ds) with
    | .ok ds => pure ds
    | .error (pos, msg) =>
      reportElpiError o ref s!"{pos.toString}: {msg}"
  -- typecheck against the program as it is so far
  match assemble (← getEnv) target ds with
  | .ok _ => pure ds
  | .error e => reportElpiError o ref (toString e)

/-- Parser for `lp%{ … }%`: a raw block, kept as one literal token. -/
def lpBlockFn : Parser.ParserFn := fun c s =>
  let input := c.input
  let startPos := s.pos
  if (String.Pos.Raw.extract input startPos (String.Pos.Raw.mk (startPos.byteIdx + 4))) != "lp%{" then
    s.mkErrorAt "lp%{ … }%" startPos
  else
    let rec scan (i : Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => none
      | f + 1 =>
        if i + 1 ≥ input.utf8ByteSize then none
        else if String.Pos.Raw.get input (String.Pos.Raw.mk i) == '}' && String.Pos.Raw.get input (String.Pos.Raw.mk (i + 1)) == '%' then some i
        else scan (i + 1) f
    match scan (startPos.byteIdx + 4) input.utf8ByteSize with
    | none => s.mkErrorAt "'}%' to close lp%{" startPos
    | some i => Parser.mkNodeToken `Elpi.Cmd.lpBlock startPos true c (s.setPos (String.Pos.Raw.mk (i + 2)))


open Parser in
def lpBlock : Parser := { fn := lpBlockFn, info := mkAtomicInfo "lpBlock" }

@[combinator_formatter lpBlock] def lpBlock.formatter : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer lpBlock] def lpBlock.parenthesizer : PrettyPrinter.Parenthesizer := pure ()

syntax (name := elpiProgramDecl) "elpi_program " ident : command
syntax (name := elpiDbDecl) "elpi_db " ident : command
syntax (name := elpiAccFile) "elpi_accumulate " ident &"file " str : command
syntax (name := elpiAccInline) "elpi_accumulate " ident lpBlock : command
syntax (name := elpiAccDb) "elpi_accumulate " ident &"db " ident : command
syntax (name := elpiQuery) "#elpi " ident lpBlock : command

register_option elpi.solutions : Nat := {
  defValue := 1
  descr := "number of solutions shown by #elpi"
}

/-- The text inside `lp%{ … }%` and where it starts in the Lean file. -/
def lpText (stx : Syntax) : String × Option String.Pos.Raw :=
  match stx.isLit? `Elpi.Cmd.lpBlock with
  | some v =>
    let inner := ((v.drop 4).dropEnd 2).toString
    (inner, stx.getPos?.map fun p => String.Pos.Raw.mk (p.byteIdx + 4))
  | none => ("", none)

@[command_elab elpiProgramDecl] def elabProgramDecl : CommandElab := fun stx => do
  let n := stx[1].getId
  if isProgram (← getEnv) n || isDb (← getEnv) n then
    throwErrorAt stx[1] "{n} is already declared as an ELPI program or database"
  modifyEnv (elpiExt.addEntry · (.program n))
  elabCommand (← `(def $(mkIdent n) : Elpi.ProgramRef := ⟨$(quote n)⟩))

@[command_elab elpiDbDecl] def elabDbDecl : CommandElab := fun stx => do
  let n := stx[1].getId
  if isProgram (← getEnv) n || isDb (← getEnv) n then
    throwErrorAt stx[1] "{n} is already declared as an ELPI program or database"
  modifyEnv (elpiExt.addEntry · (.db n))
  elabCommand (← `(def $(mkIdent n) : Elpi.ProgramRef := ⟨$(quote n)⟩))

def checkTarget (stx : Syntax) : CommandElabM Name := do
  let n := stx.getId
  let env ← getEnv
  unless isProgram env n || isDb env n do
    throwErrorAt stx "unknown ELPI program or database {n}; declare it with elpi_program or elpi_db"
  return n

-- @tg: implements:: [[openspec:lean-integration#Source accumulation]]
@[command_elab elpiAccFile] def elabAccFile : CommandElab := fun stx => do
  let target ← checkTarget stx[1]
  let path := stx[3].isStrLit?.getD ""
  let leanFile ← getFileName
  let (label, text) ← match ← liftIO (Libraries.resolve {} path leanFile) with
    | .ok (_, t) => pure (path, t)
    | .error m => throwErrorAt stx[3] "{m}"
  let ds ← processSource target { label, text } stx[3] leanFile
  modifyEnv (elpiExt.addEntry · (.unit target ds))

@[command_elab elpiAccInline] def elabAccInline : CommandElab := fun stx => do
  let target ← checkTarget stx[1]
  let (text, base?) := lpText stx[2]
  let ds ← processSource target { label := "lp%", base?, text } stx[2] (← getFileName)
  modifyEnv (elpiExt.addEntry · (.unit target ds))

@[command_elab elpiAccDb] def elabAccDb : CommandElab := fun stx => do
  let target ← checkTarget stx[1]
  let db := stx[3].getId
  unless isDb (← getEnv) db do throwErrorAt stx[3] "{db} is not an ELPI database"
  modifyEnv (elpiExt.addEntry · (.useDb target db))

/-! ### `#elpi` -/

def isReflected : Term → Bool
  | .app (.const c) _ =>
    [cConstR, cAppR, cFunR, cForallR, cLetR, cSortR, cLitR, cMVarR, cFVarR, cProjR, cMDataR].contains c
  | _ => false

/-- Show a solution; reflected terms are pretty-printed as Lean syntax inside `{{ }}`. -/
def showSolution (s : Solution) : MetaM String := do
  let mut parts : Array String := #[]
  for (n, t) in s.bindings do
    if isReflected t then
      match Reflect.ofTerm t with
      | .ok e => parts := parts.push (n ++ " = {{" ++ toString (← _root_.Lean.Meta.ppExpr e) ++ "}}")
      | .error _ => parts := parts.push s!"{n} = {s.show t}"
    else parts := parts.push s!"{n} = {s.show t}"
  let mut out := ", ".intercalate parts.toList
  for l in s.constraintLines do out := out ++ "\n" ++ l
  return out

/-- Run a query text against a program in `MetaM`; `limit` solutions at most. -/
def runQuery (env : Environment) (progName : Name) (t : STm) (phase : Host.Phase)
    (limit : Nat) (fuel : Nat := defaultFuel) (dbAcc : String → String → MetaM Unit := fun _ _ => throwError "no databases") :
    MetaM (Except ElpiError (List Solution)) := do
  match assemble env progName with
  | .error e => return .error e
  | .ok p =>
    let ref ← IO.mkRef ""
    let bs := Host.leanBuiltins { phase, dbAccumulate := dbAcc, lastError := ref }
    return ← runPrepared (m := MetaM) p (p.prepareTm t fuel) bs limit

-- @tg: implements:: [[openspec:lean-integration#Query command]]
@[command_elab elpiQuery] def elabQuery : CommandElab := fun stx => do
  let prog := stx[1].getId
  unless isProgram (← getEnv) prog do throwErrorAt stx[1] "unknown ELPI program {prog}"
  let (text, base?) := lpText stx[2]
  let o : Origin := { label := "lp%", base?, text }
  let t ← match Parser.parseQuery "lp%" text with
    | .ok t => pure t
    | .error e => reportElpiError o stx[2] e.toString
  let t ← match ← liftTermElabM (Quote.elabTm t) with
    | .ok t => pure t
    | .error (pos, m) => reportElpiError o stx[2] s!"{pos.toString}: {m}"
  let n := elpi.solutions.get (← getOptions)
  let r ← liftTermElabM (runQuery (← getEnv) prog t .query n)
  match r with
  | .error .outOfFuel => throwErrorAt stx "ELPI query ran out of fuel"
  | .error e => reportElpiError o stx[2] (toString e)
  | .ok [] => throwErrorAt stx "query has no solution"
  | .ok sols =>
    for s in sols do
      let msg ← liftTermElabM (showSolution s)
      logInfoAt stx (if msg.isEmpty then "true" else msg)

end Elpi.Cmd
