import Elpi.LF.Check
import Elpi.LF.Strategy
import Elpi.Runtime.Api

/-!
# LF proof terms

Elaboration of an LF signature into an ELPI program in which every LF predicate takes the
proof term as an extra first argument. A resolution step builds the proof by unifying the
caller's proof hole with `c X̄ D̄`; universal goals and hypotheses are the core's `pi` and
`=>`, with the hole applied to the eigenvariables. Backtracking discards partial proofs
because holes are ordinary variables of the persistent store.
-/

-- @lat: [[components#LF proof terms]]

namespace Elpi.LF

/-- The internal predicate of an LF family. -/
def lfPredName (fam : String) : String := "lf." ++ fam
def lfPred (fam : String) : ConstId := constIdOf (lfPredName fam)

/-- The family a type ends in. -/
partial def LFTy.target : LFTy → Option String
  | .atom f _ => some f
  | .pi _ _ c => c.target
  | .unk _ => none

def LFSig.role? (sig : LFSig) (fam : String) : Option FamRole := (sig.families[fam]?).map (·.2)

def LFSig.isJudgmentTy (sig : LFSig) (t : LFTy) : Bool :=
  match t.target with
  | some f => sig.role? f == some .judgment
  | none => false

/-- Map a term of a type that lives at LF depth `base`: references to the `base` outer
binders become clause variables, deeper binders move down by `base`. -/
partial def mapAt (base : Nat) : Term → Term
  | .bound l => if l < base then .cvar l #[] else .bound (l - base)
  | .app (.bound l) as =>
    let as' := as.map (mapAt base)
    if l < base then Term.mkApp (.cvar l #[]) as' else .app (.bound (l - base)) as'
  | .app h as => .app (mapAt base h) (as.map (mapAt base))
  | .lam b => .lam (mapAt base b)
  | .uvar u as => .uvar u (as.map (mapAt base))
  | t => t

/-- The goal for a premise type, with proof `proof` applied to the variables bound so far. -/
partial def premGoal (sig : LFSig) (j : Nat) (t : LFTy) (proof : Term) (depth : Nat)
    (acc : Array Term) : Except String Term := do
  match t with
  | .pi n dom cod =>
    let u := Term.bound depth
    match dom with
    | .atom f bargs =>
      if sig.role? f == some .judgment then
        -- a hypothesis: assume `lf.f u args`, with the proof being the variable itself
        let assume := Term.app (.const (lfPred f)) (#[u] ++ bargs.map (mapAt j))
        let inner ← premGoal sig j cod proof (depth + 1) (acc.push u)
        return .app (.const cPi) #[.lam (.app (.const cImpl) #[assume, inner])]
      else
        let inner ← premGoal sig j cod proof (depth + 1) (acc.push u)
        return .app (.const cPi) #[.lam inner]
    | _ => throw s!"the binder {n} has a hypothesis that is not atomic"
  | .atom f args =>
    return .app (.const (lfPred f)) (#[Term.mkApp proof acc] ++ args.map (mapAt j))
  | .unk _ => throw "internal: unknown type"

/-- The ELPI clause of a judgment constant. -/
def constClause (sig : LFSig) (c : String) (t : LFTy) : Except String ClauseItem := do
  -- peel the Π telescope
  let rec peel (t : LFTy) (acc : Array (String × LFTy)) : Array (String × LFTy) × LFTy :=
    match t with
    | .pi n d cod => peel cod (acc.push (n, d))
    | t => (acc, t)
  let (binders, head) := peel t #[]
  let .atom fam hargs := head | throw s!"{c}: the type does not end in a family"
  let k := binders.size
  -- the proof term: c applied to all its arguments
  let proof := Term.app (.const (constIdOf c)) ((List.range k).toArray.map fun i => .cvar i #[])
  let headT := Term.app (.const (lfPred fam)) (#[proof] ++ hargs.map (mapAt k))
  -- premises: judgment-typed binders, solved in reverse Π order (textual order of `<-`)
  let mut goals : Array Term := #[]
  for j in (List.range k).reverse do
    let (_, dom) := binders[j]!
    if sig.isJudgmentTy dom then
      goals := goals.push (← premGoal sig j dom (.cvar j #[]) 0 #[])
  let body : Term := match goals.toList with
    | [] => .const cTrue
    | g :: gs => gs.foldl (fun acc x => .app (.const cConj) #[acc, x]) g
  return { pred := lfPred fam
           clause := { head := headT, body, nvars := k, name? := some c } }

/-- A bridged Lean function on naturals, evaluated by the unification hook. -/
structure BridgeFn where
  arity : Nat
  fn : Array Nat → Nat

/-- The value of a ground object built from numerals and bridged functions. -/
partial def evalBridged (fns : Std.HashMap Nat BridgeFn) (deref : Term → Term) (t : Term) : Option Nat :=
  match deref t with
  | .lit (.int i) => if i ≥ 0 then some i.toNat else none
  | .app (.const c) args =>
    match fns[c.idx]? with
    | some f =>
      if f.arity != args.size then none else
      match args.mapM (evalBridged fns deref) with
      | some vs => some (f.fn vs)
      | none => none
    | none => none
  | .const c => match fns[c.idx]? with | some f => if f.arity == 0 then some (f.fn #[]) else none | none => none
  | _ => none

/-- Does an object contain unification variables (so that evaluation must wait)? -/
partial def hasFlex (deref : Term → Term) (t : Term) : Bool :=
  match deref t with
  | .uvar .. => true
  | .app h args => hasFlex deref h || args.any (hasFlex deref)
  | .lam b => hasFlex deref b
  | _ => false

/-- The unification hook of the defeq bridge: a stuck clash on a bridged head is decided by
evaluating both sides in Lean; non-ground sides wait; a syntactic success never reaches it. -/
-- @tg: implements:: [[openspec:elpi-lf#Defeq bridge]]
def bridgeHook (sig : LFSig) (fns : Std.HashMap String BridgeFn) : UnifHook :=
  let names := sig.bridges.toList.filterMap fun (n, _) => if sig.consts.contains n then some n else none
  let byId : Std.HashMap Nat BridgeFn :=
    names.foldl (init := {}) fun m n => match fns[n]? with | some f => m.insert (constIdOf n).idx f | none => m
  { interpreted := names
    onStuck := fun deref a b _ =>
      match evalBridged byId deref a, evalBridged byId deref b with
      | some x, some y => if x == y then .solved [] else .fail
      | _, _ =>
        if hasFlex deref a || hasFlex deref b then .suspend
        else if names.any (fun n => fns[n]?.isNone) then .suspend
        else .decline }

/-- The elaborated program of a signature (on top of the standard library). -/
-- @tg: implements:: [[openspec:elpi-lf#Proof term recording]]
def elaborate (sig : LFSig) (fns : Std.HashMap String BridgeFn := {}) : Except String CompiledProgram := do
  let base ← match baseProgram with
    | .ok b => pure b
    | .error e => throw (toString e)
  let mut items : Array ClauseItem := base.items
  for c in sig.order do
    if let some t := sig.consts[c]? then
      if sig.isJudgmentTy t then
        items := items.push (← constClause sig c t)
  let lists ← match graft items with
    | .ok l => pure l
    | .error e => throw (toString e)
  let mut syms := base.syms
  for n in sig.order do syms := (syms.intern n).2
  for f in sig.order do syms := (syms.intern (lfPredName f)).2
  let p : CompiledProgram := { base with items, db := Database.ofLists lists, syms }
  let hasFn := sig.bridges.toList.any fun (n, _) => sig.consts.contains n
  return if hasFn then p.withHook (bridgeHook sig fns) else p


/-! ### Queries -/

/-- An answer to an LF query: the proof term, the instantiated query and the bindings. -/
structure LFAnswer where
  proof : Term
  ty : LFTy
  bindings : List (String × Term)
  constraints : List Constraint
  syms : Symbols
  store : Store

/-- Replace the collected metavariables by clause variables (offset by one for the proof). -/
partial def toCVars (store : Store) (ms : Array UVarId) (t : Term) : Term :=
  match store.deref t 0 with
  | .uvar u as =>
    let as' := as.map (toCVars store ms)
    match ms.findIdx? (· == u) with
    | some i => Term.mkApp (.cvar (i + 1) #[]) as'
    | none => .uvar u as'
  | .app h as => .app (toCVars store ms h) (as.map (toCVars store ms))
  | .lam b => .lam (toCVars store ms b)
  | t => t

/-- The prepared machine of an LF query type. -/
structure LFQuery where
  prep : Prepared
  fam : String
  argsOf : Store → Array Term

/-- Elaborate the query `src` and build its machine on `prog`. Query variables are the
uppercase variables of the query; the proof hole is the first. -/
def prepareQuery (sig : LFSig) (prog : CompiledProgram) (src : String) (fuel : Nat) :
    Except String (Prepared × String × Array Term) := do
  let stm ← match LFSyntax.parseTyString "<query>" src with
    | .ok t => pure t
    | .error e => throw e.toString
  let (ty, cs) ← match elabQueryType sig stm with
    | .ok r => pure r
    | .error e => throw e.toString
  let .atom fam args := ty | throw "an LF query must be a judgment, not a Π type"
  let ms := cs.named.map (·.2)
  let tmpl := args.map (toCVars cs.store ms)
  let names := ["%proof"] ++ (cs.named.toList.map (·.1))
  let prep := prog.prepareRaw names (fuel := fuel) fun vs =>
    .app (.const (lfPred fam))
      (#[vs[0]!] ++ tmpl.map (Term.renameCVars vs 0))
  return (prep, fam, tmpl)

/-- Height of a proof term: nested uses of judgment constants. -/
partial def proofHeight (judg : Std.HashSet Nat) : Term → Nat
  | .const c => if judg.contains c.idx then 1 else 0
  | .app (.const c) args =>
    (if judg.contains c.idx then 1 else 0) + args.foldl (fun m a => max m (proofHeight judg a)) 0
  | .app h args => args.foldl (fun m a => max m (proofHeight judg a)) (proofHeight judg h)
  | .lam b => proofHeight judg b
  | _ => 0

/-- Run one strategy over an LF query; an exhausted run asks the strategy for the next one
(sharing the fuel), so finite failure is reported only by a run without cutoff. -/
partial def lfSearch (judg : Std.HashSet Nat) (famName : String) (tmpl : Array Term)
    (baseEnv : _root_.Elpi.Env Id) (syms : Symbols) (names : Array (String × UVarId))
    (strategy : Strategy) (M0 : Machine Unit) : LazyList (Except ElpiError LFAnswer) :=
  let env := { baseEnv with bound := strategy.bound }
  let rec go (M : Machine Unit) : LazyList (Except ElpiError LFAnswer) :=
    match Id.run (runLoop env M) with
    | .yield sol M' =>
      let st := sol.store
      let vars := names.map fun (_, u) => Term.uvar u #[]
      let proof := st.zonk vars[0]! 0
      if strategy.admits (proofHeight judg proof) then
        let args := tmpl.map fun t => st.zonk (Term.renameCVars vars 0 t) 0
        let ans : LFAnswer :=
          { proof, ty := .atom famName args
            bindings := (names.toList.drop 1).map fun (n, u) => (n, st.zonk (.uvar u #[]) 0)
            constraints := sol.constraints, syms, store := st }
        .cons (.ok ans) (Thunk.mk fun _ => go M')
      else go M'
    | .exhausted cutoff fuel =>
      match strategy.next? cutoff with
      | some s' => lfSearch judg famName tmpl baseEnv syms names s' { M0 with fuel }
      | none => .nil
    | .outOfFuel => .cons (.error .outOfFuel) (Thunk.mk fun _ => .nil)
    | .error e => .cons (.error e) (Thunk.mk fun _ => .nil)
  go M0

/-- The judgment constants of a signature (the ones that build proof terms). -/
def LFSig.judgmentConsts (sig : LFSig) : Std.HashSet Nat :=
  sig.consts.fold (init := {}) fun s n t => if sig.isJudgmentTy t then s.insert (constIdOf n).idx else s

-- @tg: implements:: [[openspec:elpi-lf#Pattern unification for LF]]
def runQuery (sig : LFSig) (prog : CompiledProgram) (src : String) (fuel : Nat := defaultFuel)
    (strategy : Option Strategy := none) : LazyList (Except ElpiError LFAnswer) :=
  match prepareQuery sig prog src fuel with
  | .error m => .cons (.error (.load m)) (Thunk.mk fun _ => .nil)
  | .ok (prep, fam, tmpl) =>
    let st := strategy.getD (match sig.strategy with | some d => Strategy.ofDirective d | none => dfs)
    let lfp : Std.HashSet Nat := sig.families.fold (init := {}) fun s n _ => s.insert (lfPred n).idx
    let env := { prog.env Id prep.syms with lfPreds := lfp }
    lfSearch sig.judgmentConsts fam tmpl env prep.syms prep.names st prep.machine

/-- Print an LF object: binders are named `x<level>`, outer binders by `names`. -/
partial def showObj (syms : Symbols) (store : Store) (names : Array String) (t : Term)
    (depth : Nat) (top : Bool := true) : String :=
  let wrap (s : String) := if top then s else "(" ++ s ++ ")"
  match t with
  | .bound l => if h : l < names.size then names[l] else s!"x{l}"
  | .const c => syms.name c
  | .app h #[] => showObj syms store names h depth top
  | .app h as =>
    wrap (showObj syms store names h depth false ++ " " ++
      " ".intercalate (as.toList.map fun a => showObj syms store names a depth false))
  | .lam b => wrap s!"x{depth}\\ {showObj syms store names b (depth + 1) true}"
  | t => ppTm syms store t depth

/-- Print an LF type with the given names for its outer binders. -/
partial def showTy (syms : Symbols) (store : Store) (names : Array String) : LFTy → String
  | .atom a as =>
    a ++ as.foldl (fun s t => s ++ " " ++ showObj syms store names t names.size false) ""
  | .pi n dom cod =>
    let ds := match dom with
      | .pi .. => "(" ++ showTy syms store names dom ++ ")"
      | _ => showTy syms store names dom
    if n != "_" && !n.isEmpty then
      s!"pi {n}:{showTy syms store names dom}\\ {showTy syms store (names.push n) cod}"
    else s!"{ds} -> {showTy syms store (names.push "_") cod}"
  | .unk i => s!"?{i}"

def LFAnswer.showTerm (a : LFAnswer) (t : Term) : String := showObj a.syms a.store #[] t 0

def LFAnswer.showProof (a : LFAnswer) : String := a.showTerm a.proof

def LFAnswer.showBindings (a : LFAnswer) : String :=
  ", ".intercalate (a.bindings.map fun (n, t) => s!"{n} = {a.showTerm t}")

end Elpi.LF
