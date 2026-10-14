import Lean
import Elpi.Core.Builtins
import Elpi.Lean.Reflect
import Elpi.Lean.Marshal

/-!
# Lean builtins

The `MetaM` host-monad instance: a choice point snapshots the full `Meta.SavedState`, so
backtracking rewinds metavariable assignments and the message log together with ELPI
bindings. This is the only module of the engine core's neighbourhood that depends on
`Lean.Meta`; the core (`Elpi/Core/*`) must not import it.

It also provides the `lean.*` builtins that run in `MetaM`: they take and return reflected
terms and delegate to `inferType`, `whnf`, `isDefEq`, the term elaborator, `mkFreshExprMVar`,
`ppExpr` and `addDecl`.
-/

-- @lat: [[components#Lean builtins]]

namespace Elpi.Host

open _root_.Lean Meta Elab

-- @tg: implements:: [[openspec:elpi-core-engine#Monad-generic engine]]
instance : Elpi.Backtrackable MetaM Meta.SavedState :=
  ⟨Meta.saveState, fun s => s.restore⟩

instance : Elpi.Output MetaM := ⟨fun s => IO.print s⟩

/-- What an ELPI execution may do to Lean: fixed for the whole execution. -/
inductive Phase where
  | query | tactic | command | runtime
  deriving BEq, Repr, Inhabited

def Phase.toString : Phase → String
  | .query => "query" | .tactic => "tactic" | .command => "command" | .runtime => "runtime"

/-- Configuration of one execution's builtins; `phase` is fixed for the whole execution and
the environment-changing builtins check it. -/
-- @tg: implements:: [[openspec:lean-integration#Phase-restricted effects]]
structure Config where
  phase : Phase := .query
  /-- Implementation of `lean.db.accumulate` (commands only). -/
  dbAccumulate : String → String → MetaM Unit := fun _ _ => throwError "no database support"
  /-- Message of the last exception swallowed by a builtin. -/
  lastError : IO.Ref String

def cInductInfo : ConstId := ⟨symbolId "inductinfo"⟩
def cCtorInfo : ConstId := ⟨symbolId "ctorinfo"⟩
def cConstInfo : ConstId := ⟨symbolId "constinfo"⟩
def cLeanDef : ConstId := ⟨symbolId "lean.def"⟩
def cLeanInst : ConstId := ⟨symbolId "lean.inst"⟩

private def one (c : BCtx) (args : Array Term) : BResult :=
  .alts c.store (.cons args (Thunk.mk fun _ => .nil))

/-- Reify an argument (fully dereferenced) at the current depth. -/
private def argExpr (c : BCtx) (t : Term) : Except String Expr :=
  Reflect.ofTermAt (fun _ => .error "an unassigned ELPI variable in a Lean term") (c.store.zonk t c.depth) c.depth

private def reflectExpr (c : BCtx) (e : Expr) : Except String Term :=
  Reflect.toTermAt {} e c.depth

/-- Run `act`; an exception becomes failure and is remembered for `lean.last-error`. -/
private def guarded (cfg : Config) (c : BCtx) (act : MetaM BResult) : MetaM BResult := do
  try act
  catch e =>
    cfg.lastError.set (← e.toMessageData.toString)
    return .fail

private def sig (name : String) (modes : List Mode) : BuiltinSig :=
  { name, modes := modes.toArray, type := .con "any" [] }

private def withExpr (cfg : Config) (c : BCtx) (t : Term) (k : Expr → MetaM BResult) :
    MetaM BResult :=
  match argExpr c t with
  | .ok e => guarded cfg c (k e)
  | .error m => do cfg.lastError.set m; return .fail

private def reply (c : BCtx) (args : Array Term) (i : Nat) (e : Expr) : MetaM BResult :=
  match reflectExpr c e with
  | .ok t => return one c (args.set! i t)
  | .error m => throwError m

/-- Elaborate Lean source text as a term. -/
def elabSource (src : String) (expected : Option Expr) : MetaM Expr := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error m => throwError "{m}"
  Term.TermElabM.run' do
    let e ← Term.elabTerm stx expected
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- The `lean.*` builtins, in `MetaM`. -/
-- @tg: implements:: [[openspec:lean-integration#Lean builtins]]
def leanBuiltins (cfg : Config) : List (Builtin MetaM) :=
  let mk (name : String) (modes : List Mode) (run : BCtx → Array Term → MetaM BResult) :
      Builtin MetaM := { sig := sig name modes, run }
  [ mk "lean.infer" [.i, .o] fun c args =>
      withExpr cfg c args[0]! fun e => do reply c args 1 (← inferType e),
    mk "lean.whnf" [.i, .o] fun c args =>
      withExpr cfg c args[0]! fun e => do reply c args 1 (← whnf e),
    mk "lean.defeq" [.i, .i] fun c args =>
      withExpr cfg c args[0]! fun a =>
        match argExpr c args[1]! with
        | .error m => do cfg.lastError.set m; return .fail
        | .ok b => do
          if ← isDefEq a b then return one c args else return .fail,
    mk "lean.mk_mvar" [.i, .o] fun c args =>
      withExpr cfg c args[0]! fun ty => do reply c args 1 (← mkFreshExprMVar (some ty)),
    mk "lean.pp" [.i, .o] fun c args =>
      withExpr cfg c args[0]! fun e => do
        let s := toString (← ppExpr e)
        return one c (args.set! 1 (.lit (.str s))),
    mk "lean.elab" [.i, .i, .o] fun c args =>
      match c.store.deref args[0]! c.depth with
      | .lit (.str src) => guarded cfg c do
        let expected ← match c.store.deref args[1]! c.depth with
          | .uvar .. => pure none
          | t => match argExpr c t with
            | .ok e => pure (some e)
            | .error m => throwError m
        reply c args 2 (← elabSource src expected)
      | _ => return .error "lean.elab: the source must be a string",
    mk "lean.env.find" [.i, .o] fun c args =>
      match Reflect.opaqueOf "name" (c.store.deref args[0]! c.depth) with
      | .error m => return .error s!"lean.env.find: {m}"
      | .ok d => guarded cfg c do
        let n := Reflect.nameDec d
        match (← getEnv).find? n with
        | some (.inductInfo iv) =>
          let ctors ← iv.ctors.mapM fun cn => do
            let some (.ctorInfo cv) := (← getEnv).find? cn | throwError "missing constructor {cn}"
            pure (Term.app (.const cCtorInfo) #[Reflect.nameTerm cn, .lit (.int cv.numFields)])
          let info := Term.app (.const cInductInfo) #[Reflect.listTerm ctors, .lit (.int iv.numParams)]
          return one c (args.set! 1 info)
        | some ci =>
          match reflectExpr c ci.type with
          | .ok t => return one c (args.set! 1 (Term.app (.const cConstInfo) #[t]))
          | .error m => throwError m
        | none => return .fail,
    mk "lean.add_decl" [.i] fun c args => do
      unless cfg.phase == .command do
        return .error s!"lean.add_decl is only available in commands (current phase: {cfg.phase.toString})"
      match c.store.zonk args[0]! c.depth with
      | .app (.const k) #[nm, ty, v] =>
        if k != cLeanDef && k != cLeanInst then return .error "lean.add_decl: bad declaration"
        match Reflect.opaqueOf "name" nm, argExpr c ty, argExpr c v with
        | .ok nd, .ok tye, .ok ve => guarded cfg c do
          let n := Reflect.nameDec nd
          let tye ← instantiateMVars tye
          let ve ← instantiateMVars ve
          let lps := (collectLevelParams {} tye |> fun s => collectLevelParams s ve).params.toList
          addAndCompile <| .defnDecl
            { name := n, levelParams := lps, type := tye, value := ve, hints := .abbrev, safety := .safe }
          if k == cLeanInst then addInstance n AttributeKind.global 1000
          return one c args
        | _, _, _ => return .error "lean.add_decl: bad declaration"
      | _ => return .error "lean.add_decl: bad declaration",
    mk "lean.db.accumulate" [.i, .i] fun c args => do
      unless cfg.phase == .command do
        return .error s!"lean.db.accumulate is only available in commands (current phase: {cfg.phase.toString})"
      match c.store.deref args[0]! c.depth, c.store.deref args[1]! c.depth with
      | .lit (.str db), .lit (.str clause) => guarded cfg c do
        cfg.dbAccumulate db clause
        return one c args
      | _, _ => return .error "lean.db.accumulate: strings expected",
    mk "lean.last-error" [.o] fun c args => do
      let m ← cfg.lastError.get
      return one c (args.set! 0 (.lit (.str m))),
    mk "lean.name->string" [.i, .o] fun c args =>
      match Reflect.opaqueOf "name" (c.store.deref args[0]! c.depth) with
      | .ok d => return one c (args.set! 1 (.lit (.str (Reflect.nameDec d).toString)))
      | .error m => return .error s!"lean.name->string: {m}",
    mk "lean.error" [.i] fun c args =>
      match c.store.deref args[0]! c.depth with
      | .lit (.str m) => return .error m
      | _ => return .error "lean.error: string expected",
    mk "lean.fresh-fvar" [.i, .o] fun c args => do
      match c.store.deref args[0]! c.depth with
      | .lit (.str s) =>
        let id ← mkFreshFVarId
        let t := Term.app (.const cFVarR) #[Reflect.mkOpaque "fvarid" (Reflect.nameEnc id.name)]
        let _ := s
        return one c (args.set! 1 t)
      | _ => return .error "lean.fresh-fvar: string expected",
    mk "lean.binder-named" [.i, .i, .o] fun c args =>
      match c.store.deref args[0]! c.depth, Reflect.opaqueOf "binder" (c.store.deref args[1]! c.depth) with
      | .lit (.str s), .ok d =>
        match Reflect.binderDec d with
        | some (_, bi, nd) => return one c (args.set! 2 (Reflect.binderTerm s.toName bi nd))
        | none => return .error "lean.binder-named: bad binder"
      | _, _ => return .error "lean.binder-named: a string and a binder expected",
    mk "lean.inst-mvars" [.i, .o] fun c args =>
      withExpr cfg c args[0]! fun e => do reply c args 1 (← instantiateMVars e),
    mk "lean.string->name" [.i, .o] fun c args =>
      match c.store.deref args[0]! c.depth with
      | .lit (.str s) => return one c (args.set! 1 (Reflect.nameTerm s.toName))
      | _ => return .error "lean.string->name: string expected" ]

end Elpi.Host
