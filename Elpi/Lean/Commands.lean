import Lean
import Elpi.Lean.Libraries

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
  names : Array String
  consts : List (String × Nat × Ty)
  modes : List (String × Array Mode)
  items : Array (Nat × Term × Term × Nat × Option String × Pos × Option String × Option String)

def ProgramData.ofProgram (p : CompiledProgram) : ProgramData :=
  { names := p.syms.names
    consts := p.sig.consts.toList.map fun (n, sc) => (n, sc.nvars, sc.ty)
    modes := p.sig.modes.toList
    items := p.items.map fun it =>
      (it.pred.idx, it.clause.head, it.clause.body, it.clause.nvars, it.clause.name?,
       it.clause.pos, it.before?, it.after?) }

def ProgramData.toProgram (d : ProgramData) : CompiledProgram :=
  let syms : Symbols :=
    { names := d.names
      ids := d.names.foldl (init := ({} : Std.HashMap String Nat)) fun m n =>
        m.insert n m.size }
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
