import Lean
import Elpi.Lean.Commands

/-!
# Tactic bridge

`elpi_tactic name := P` registers an ELPI-backed tactic invoked as `by elpi name args`; each
main goal is reflected, the ELPI predicate `solve` is run in `MetaM`, the proof is reified
(leftover ELPI variables become metavariables), checked with `isDefEq` against the goal and
assigned. Also the ELPI commands (`elpi_command`, `elpi_export`) and the programmatic API
`Elpi.query`.
-/

-- @lat: [[components#Tactic bridge]]

namespace Elpi.Cmd

open _root_.Lean Elab Command Tactic Meta

declare_syntax_cat elpiArg
syntax num : elpiArg
syntax str : elpiArg
syntax ident : elpiArg
syntax "(" term ")" : elpiArg

syntax (name := elpiTacDecl) "elpi_tactic " ident " := " ident : command
syntax (name := elpiCmdDecl) "elpi_command " ident " := " ident : command
syntax (name := elpiExportDecl) "elpi_export " ident : command
syntax (name := elpiTac) "elpi " ident (ppSpace colGt elpiArg)* : tactic
syntax (name := elpiRunCmd) "elpi " ident (ppSpace colGt elpiArg)* : command

private def sym (n : String) : ConstId := ⟨symbolId n⟩

/-- Reflect an elaborated term (metavariables stay ELPI `mvar` values). -/
def reflectE (e : Expr) : MetaM Term := do
  match Reflect.toTerm (← instantiateMVars e) with
  | .ok t => return t
  | .error m => throwError "cannot reflect the term: {m}"

/-- An `argument` of the tactic/command interface. -/
def elabArg (stx : Syntax) : TermElabM Term := do
  match stx.getKind with
  | `Elpi.Cmd.elpiArg_1 => pure ()
  | _ => pure ()
  let s := stx
  if let some n := s[0].isNatLit? then
    return .app (.const cIntArgR) #[.lit (.int n)]
  else if let some str := s[0].isStrLit? then
    return .app (.const cStrLitR) #[.lit (.str str)]
  else
    let tstx : Syntax := if s[0].isIdent then s[0] else s[1]
    let e ← Term.elabTerm tstx none
    Term.synthesizeSyntheticMVarsNoPostponing
    return .app (.const cTrmArgR) #[← reflectE e]

def elabArgs (args : Array Syntax) : TermElabM Term := do
  return Reflect.listTerm (← args.toList.mapM elabArg)

@[command_elab elpiTacDecl] def elabTacDecl : CommandElab := fun stx => do
  let prog := stx[3].getId
  unless isProgram (← getEnv) prog do throwErrorAt stx[3] "unknown ELPI program {prog}"
  modifyEnv (elpiExt.addEntry · (.tactic stx[1].getId prog))

@[command_elab elpiCmdDecl] def elabCmdDecl : CommandElab := fun stx => do
  let prog := stx[3].getId
  unless isProgram (← getEnv) prog do throwErrorAt stx[3] "unknown ELPI program {prog}"
  modifyEnv (elpiExt.addEntry · (.command stx[1].getId prog))

def findTactic (env : Environment) (n : Name) : Option Name :=
  (elpiEntries env).findSome? fun | .tactic m p => if m == n then some p else none | _ => none

def findCommand (env : Environment) (n : Name) : Option Name :=
  (elpiEntries env).findSome? fun | .command m p => if m == n then some p else none | _ => none

/-- Reflect the local context of the current goal. -/
def reflectCtx : MetaM Term := do
  let mut ds : List Term := []
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← reflectE d.type
    ds := ds ++ [Term.app (.const cDeclR)
      #[.app (.const cFVarR) #[Reflect.mkOpaque "fvarid" (Reflect.nameEnc d.fvarId.name)],
        Reflect.nameTerm d.userName, ty]]
  return Reflect.listTerm ds

/-- Reify a (fully dereferenced) term in `MetaM`: like `Reflect.ofTermAt`, and in addition the
pseudo-constructor `lean.lam-fvar F B T Body`, which abstracts the free variable `F` from the
body with `mkLambdaFVars`, so metavariables in the body get their delayed assignments. -/
partial def reifyM (onVar : UVarId → Except String Expr) (t : Term) (d0 : Nat) (k : Nat := 0) :
    MetaM Expr := do
  let some pseudo := some (sym "lean.lam-fvar") | unreachable!
  match t with
  | .app (.const c) args =>
    if c == pseudo && args.size == 4 then
      let fid : FVarId := ⟨Reflect.nameDec (← liftExcept (Reflect.opaqueOf "fvarid" args[0]!))⟩
      let some (n, bi, _) := Reflect.binderDec (← liftExcept (Reflect.opaqueOf "binder" args[1]!))
        | throwError "bad binder"
      let ty ← reifyM onVar args[2]! d0 k
      withLCtx ((← getLCtx).mkLocalDecl fid n ty bi) (← getLocalInstances) do
        let body ← reifyM onVar args[3]! d0 k
        mkLambdaFVars #[Expr.fvar fid] body
    else if c == cAppR && args.size == 2 then
      let h ← reifyM onVar args[0]! d0 k
      let as ← (← liftExcept (Reflect.listElems args[1]!)).mapM (reifyM onVar · d0 k)
      return mkAppN h as.toArray
    else if (c == cFunR || c == cForallR) && args.size == 3 then
      let some (n, bi, _) := Reflect.binderDec (← liftExcept (Reflect.opaqueOf "binder" args[0]!))
        | throwError "bad binder"
      let ty ← reifyM onVar args[1]! d0 k
      let b := match args[2]! with
        | .lam x => x
        | f => Term.applyAt (f.shiftUp (d0 + k) 1) #[.bound (d0 + k)] (d0 + k + 1)
      let body ← reifyM onVar b d0 (k + 1)
      return if c == cFunR then .lam n ty body bi else .forallE n ty body bi
    else liftExcept (Reflect.ofTermAt onVar t d0 k)
  | _ => liftExcept (Reflect.ofTermAt onVar t d0 k)
where
  liftExcept {α : Type} (x : Except String α) : MetaM α :=
    match x with
    | .ok a => pure a
    | .error m => throwError "{m}"

/-- Run the ELPI predicate `solve` of `prog` on one goal. -/
def solveGoal (env : Environment) (prog : Name) (name : Name) (g : MVarId) (args : Term) :
    TacticM (List MVarId) := do
  g.withContext do
    let goalTy ← instantiateMVars (← g.getType)
    let ctx ← reflectCtx
    let tyT ← reflectE goalTy
    let p ← match assemble env prog with
      | .ok p => pure p
      | .error e => throwError "{e}"
    let ref ← IO.mkRef ""
    let bs := Host.leanBuiltins { phase := .tactic, lastError := ref }
    let prep := p.prepareRaw ["P", "Gs"] fun vs =>
      .app (.const (sym "solve"))
        #[.app (.const cGoalR) #[ctx, vs[0]!, tyT], args, vs[1]!]
    let r ← runPrepared (m := MetaM) p (.ok prep) bs 1
    match r with
    | .error e => throwError "tactic {name} failed: {e}"
    | .ok [] =>
      let why := (← ref.get)
      throwError "tactic {name} failed: solve has no solution{if why.isEmpty then "" else s!" ({why})"}"
    | .ok (sol :: _) =>
      let st := sol.store
      let some pT := sol.bindings.lookup "P" | throwError "internal: no proof"
      let some gsT := sol.bindings.lookup "Gs" | throwError "internal: no goals"
      let gs ← match Reflect.listElems gsT with
        | .ok l => pure l
        | .error m => throwError "tactic {name}: solve returned a malformed goal list ({m})"
      -- a returned goal is `goal Ctx A Ty`: A an unassigned ELPI variable (a new goal) or a
      -- Lean metavariable (an argument left open by `apply`)
      let mut proofVars : List (UVarId × Term × Term) := []   -- (A, Ctx, Ty)
      let mut openMVars : List MVarId := []
      for gt in gs do
        match gt with
        | .app (.const c) #[cx, .uvar u #[], ty] =>
          if c == cGoalR then proofVars := proofVars ++ [(u, cx, ty)]
          else throwError "tactic {name}: malformed goal"
        | .app (.const c) #[_, .app (.const m) #[.builtinData o], _] =>
          if c == cGoalR && m == cMVarR then openMVars := openMVars ++ [⟨Reflect.nameDec o.data⟩]
          else throwError "tactic {name}: malformed goal"
        | _ => throwError "tactic {name}: a returned goal must be `goal Ctx A Ty` with an unassigned proof variable"
      let isProof (u : UVarId) := proofVars.any (·.1 == u)
      let mut vmap : Std.HashMap UVarId Expr := {}
      let allVars := proofVars.foldl (init := Unify.collectUVars st pT 0) fun a (_, _, ty) =>
        Unify.collectUVars st ty 0 a
      for u in allVars do
        unless isProof u do
          vmap := vmap.insert u (← mkFreshExprMVar none)
      let onVar (vm : Std.HashMap UVarId Expr) : UVarId → Except String Expr := fun u =>
        match vm[u]? with
        | some e => .ok e
        | none => .error "an ELPI variable has no metavariable"
      let mut newGoals : List MVarId := []
      for (u, cx, ty) in proofVars do
        let tyE ← match Reflect.ofTerm (st.zonk ty 0) (onVar vmap) with
          | .ok e => pure e
          | .error m => throwError "tactic {name}: cannot reify a goal type ({m})"
        -- the goal's context: the current one plus the free variables its hypotheses introduce
        let mut lctx ← getLCtx
        match Reflect.listElems (st.zonk cx 0) with
        | .ok ds =>
          for d in ds do
            match d with
            | .app (.const dc) #[.app (.const fc) #[.builtinData fo], nm, dty] =>
              if dc == cDeclR && fc == cFVarR then
                let fid : FVarId := ⟨Reflect.nameDec fo.data⟩
                unless lctx.contains fid do
                  let n := match Reflect.opaqueOf "name" nm with
                    | .ok d => Reflect.nameDec d | .error _ => `h
                  match Reflect.ofTerm (st.zonk dty 0) (onVar vmap) with
                  | .ok te => lctx := lctx.mkLocalDecl fid n te
                  | .error m => throwError "tactic {name}: cannot reify a hypothesis ({m})"
            | _ => pure ()
        | .error _ => pure ()
        let m ← withLCtx lctx (← getLocalInstances) (mkFreshExprSyntheticOpaqueMVar tyE)
        vmap := vmap.insert u m
        newGoals := newGoals ++ [m.mvarId!]
      let pf ← reifyM (onVar vmap) (st.zonk pT 0) 0
      let pfTy ← inferType pf
      unless ← isDefEq pfTy goalTy do
        throwError "type mismatch\n  {pf}\nhas type\n  {pfTy}\nbut is expected to have type\n  {goalTy}"
      g.assign pf
      return newGoals ++ openMVars

-- @tg: implements:: [[openspec:lean-integration#ELPI tactics]]
@[tactic elpiTac] def evalElpiTac : Tactic := fun stx => do
  let name := stx[1].getId
  let env ← getEnv
  let some prog := findTactic env name | throwErrorAt stx[1] "unknown ELPI tactic {name}"
  let args ← elabArgs stx[2].getArgs
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    out := out ++ (← solveGoal env prog name g args)
  setGoals out

/-! ### Commands -/

/-- Run `main Args` of an ELPI command in `CommandElabM`. -/
def runElpiCommand (name : Name) (prog : Name) (argStx : Array Syntax) (ref : Syntax) :
    CommandElabM Unit := do
  let env ← getEnv
  let args ← liftTermElabM (elabArgs argStx)
  let dbAcc (db clause : String) : MetaM Unit := do
    let dbName := db.toName
    unless isDb (← getEnv) dbName do throwError "{db} is not an ELPI database"
    match Parser.parseProgram "lp%" clause with
    | .ok ds => modifyEnv (elpiExt.addEntry · (.unit dbName ds))
    | .error e => throwError "{e.toString}"
  let r ← liftTermElabM do
    match assemble env prog with
    | .error e => return Except.error e
    | .ok p =>
      let lastErr ← IO.mkRef ""
      let bs := Host.leanBuiltins { phase := .command, dbAccumulate := dbAcc, lastError := lastErr }
      let prep := p.prepareRaw [] fun _ => .app (.const (sym "main")) #[args]
      runPrepared (m := MetaM) p (.ok prep) bs 1
  match r with
  | .error e => throwErrorAt ref "{name}: {e}"
  | .ok [] => throwErrorAt ref "command {name} failed"
  | .ok _ => pure ()

-- @tg: implements:: [[openspec:lean-integration#ELPI commands and export]]
@[command_elab elpiRunCmd] def elabRunCmd : CommandElab := fun stx => do
  let name := stx[1].getId
  let some prog := findCommand (← getEnv) name | throwErrorAt stx[1] "unknown ELPI command {name}"
  runElpiCommand name prog stx[2].getArgs stx

/-- `elpi_export name` makes `name args` a top-level command. -/
@[command_elab elpiExportDecl] def elabExport : CommandElab := fun stx => do
  let name := stx[1].getId
  let some prog := findCommand (← getEnv) name | throwErrorAt stx[1] "unknown ELPI command {name}"
  let tok := Syntax.mkStrLit (name.toString ++ " ")
  let kindId := mkIdent (`Elpi.Cmd ++ (name.toString.replace "." "_" ++ "_cmd").toName)
  let elabId := mkIdent (`Elpi.Cmd ++ (name.toString.replace "." "_" ++ "_elab").toName)
  elabCommand (← `(syntax (name := $kindId) $tok:str (ppSpace colGt elpiArg)* : command))
  elabCommand (← `(@[command_elab $kindId] def $elabId : CommandElab := fun stx =>
    runElpiCommand $(quote name) $(quote prog) stx[1].getArgs stx))

end Elpi.Cmd

namespace Elpi

open _root_.Lean Meta

/-- The lazy stream behind `query`: each force runs the engine on the stream's private
copies of the Core / Meta state. -/
unsafe def queryGoUnsafe (syms : Symbols) (names : Array (String × UVarId)) (envM : Env MetaM)
    (ctxM : Meta.Context) (ctxC : Core.Context) (mRef : IO.Ref Meta.State)
    (cRef : IO.Ref Core.State) (M : Machine Meta.SavedState) :
    LazyList (Except ElpiError Solution) :=
  let act : MetaM (Step Meta.SavedState) := runLoop envM M
  match unsafeBaseIO (((act ctxM mRef) ctxC cRef).toBaseIO) with
  | .error _ => .cons (.error (.runtime "Lean exception inside the query")) (Thunk.mk fun _ => .nil)
  | .ok (.yield sol M') =>
    .cons (.ok (mkSolution syms names sol))
      (Thunk.mk fun _ => queryGoUnsafe syms names envM ctxM ctxC mRef cRef M')
  | .ok (.exhausted _ _) => .nil
  | .ok .outOfFuel => .cons (.error .outOfFuel) (Thunk.mk fun _ => .nil)
  | .ok (.error e) => .cons (.error e) (Thunk.mk fun _ => .nil)

@[implemented_by queryGoUnsafe]
opaque queryGo (syms : Symbols) (names : Array (String × UVarId)) (envM : Env MetaM)
    (ctxM : Meta.Context) (ctxC : Core.Context) (mRef : IO.Ref Meta.State)
    (cRef : IO.Ref Core.State) (M : Machine Meta.SavedState) :
    LazyList (Except ElpiError Solution)

/-- Run a query from `MetaM`: a lazy stream of solutions. Each element runs the engine on
demand, in the `MetaM` state the stream was created in; the phase is `query`. -/
-- @tg: implements:: [[openspec:lean-integration#Programmatic meta API]]
def query (p : ProgramRef) (q : String) (fuel : Nat := defaultFuel) :
    MetaM (LazyList (Except ElpiError Solution)) := do
  let env ← getEnv
  let some _ := (Cmd.elpiEntries env).find? fun | .program n => n == p.name | _ => false
    | throwError "unknown ELPI program {p.name}"
  let t ← match Parser.parseQuery "<query>" q with
    | .ok t => pure t
    | .error e => throwError "{e.toString}"
  let t ← match ← Elab.Term.TermElabM.run' (Quote.elabTm t) with
    | .ok t => pure t
    | .error (pos, m) => throwError "{pos.toString}: {m}"
  let prog ← match Cmd.assemble env p.name with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let ref ← IO.mkRef ""
  let bs := Host.leanBuiltins { phase := .query, lastError := ref }
  match prog.prepareTm t fuel with
  | .error e => return .cons (.error e) (Thunk.mk fun _ => .nil)
  | .ok prep =>
    let envM : Env MetaM := { prog.env MetaM prep.syms with
      builtins := bs.foldl (init := (prog.env MetaM prep.syms).builtins) fun h b =>
        match prep.syms.find? b.sig.name with
        | some c => h.insert c.idx b
        | none => h }
    -- the stream owns private copies of the Core / Meta state
    let ctxC ← readThe Core.Context
    let ctxM ← readThe Meta.Context
    let cRef ← IO.mkRef (← getThe Core.State)
    let mRef ← IO.mkRef (← getThe Meta.State)
    return queryGo prep.syms prep.names envM ctxM ctxC mRef cRef
      { goals := prep.machine.goals, store := prep.machine.store, fuel := prep.machine.fuel }

end Elpi
