import Std.Data.HashMap
import Std.Data.HashSet
import Elpi.Core.Store
import Elpi.Core.Unify
import Elpi.Core.Index
import Elpi.Core.Builtins
import Elpi.Core.CHR

/-!
# Abstract machine

An explicit first-order machine for hereditary Harrop goals: the goal stack, the choice
stack and the cut barriers are heap data, so ELPI recursion depth is not bounded by the
native stack. Choice points keep a `Store.checkpoint` and a host-monad snapshot. While the
machine runs, the store is its own parameter rather than a field, so that nothing else holds
a reference and the store's arrays are updated in place.
-/

-- @lat: [[components#Abstract machine]]

namespace Elpi

/-- A goal to solve, closed over the depth and local program it runs under. -/
structure Frame where
  goal : Term
  depth : Nat
  locals : Locals
  /-- Choice-stack height to cut back to (cut barrier). -/
  cutTo : Nat
  /-- Derivation depth, consulted only for LF goals (search strategies). -/
  ldepth : Nat := 0
  deriving Inhabited

/-- A clause candidate for a call. -/
inductive Cand where
  | static (c : Clause)
  | local (lc : LocalClause)
  deriving Inhabited

/-- What a choice point will try when backtracked into. -/
inductive Alt where
  /-- The second branch of a disjunction. -/
  | frame (f : Frame)
  /-- Remaining candidate clauses of a call. -/
  | clauses (call : Frame) (cands : Array Cand) (next : Nat)
  /-- Remaining alternatives of a builtin. -/
  | stream (call : Frame) (rest : LazyList (Array Term))
  deriving Inhabited

structure ChoicePoint (σ : Type) where
  goals : List Frame
  /-- A `Store.checkpoint`: the live store is brought back to it with `Store.undo`. -/
  store : Store
  host : σ
  alt : Alt
  deriving Inhabited

-- @tg: implements:: [[openspec:elpi-core-engine#Abstract machine]]
structure Machine (σ : Type) where
  goals : List Frame := []
  choices : Array (ChoicePoint σ) := #[]
  store : Store := {}
  fuel : Nat := 100000000
  /-- The previous solution was yielded: the next step backtracks. -/
  resume : Bool := false
  /-- Some LF goal was pruned by the depth bound (not undone by backtracking). -/
  cutoff : Bool := false
  deriving Inhabited

/-- Take the store out of the machine (leaving an empty one) so the caller holds the only
reference and the store's arrays are updated in place rather than copied. -/
@[inline] def Machine.takeStore {σ : Type} (M : Machine σ) : Store × Machine σ :=
  let s := M.store
  (s, { M with store := {} })

/-- Static environment of a run. -/
structure Env (m : Type → Type) where
  syms : Symbols
  db : Database
  modes : Std.HashMap Nat (Array Mode)
  builtins : Std.HashMap Nat (Builtin m)
  /-- CHR blocks, in source order. -/
  blocks : Array ConstraintBlock := #[]
  /-- Native handlers by the index of each predicate they own. -/
  handlers : Std.HashMap Nat (String × ConstraintHandler) := {}
  /-- LF predicates (by constant index) and the derivation depth bound for them. -/
  lfPreds : Std.HashSet Nat := {}
  bound : Option Nat := none

/-- A raw solution: the final store and the constraints still suspended in it. -/
structure RawSolution where
  store : Store
  constraints : List Constraint := []
  deriving Inhabited

inductive Step (σ : Type) where
  | yield (s : RawSolution) (resume : Machine σ)
  /-- The search space is exhausted; `cutoff` tells whether a depth bound pruned anything. -/
  | exhausted (cutoff : Bool) (fuel : Nat)
  | outOfFuel
  | error (e : ElpiError)

/-- Result of one machine step. While the machine runs, its store travels beside it as its own
value (`Machine.store` is empty then), so that nothing else holds a reference to it and the
store's arrays are updated in place; `Machine.takeStore` and `{ M with store := s }` convert at
the boundaries. -/
inductive SR (σ : Type) where
  | cont (M : Machine σ) (s : Store)
  | done (r : Step σ)

instance {σ : Type} : Inhabited (SR σ) := ⟨.done (.exhausted false 0)⟩
instance {σ : Type} : Inhabited (Step σ) := ⟨.exhausted false 0⟩

namespace Machine

/-- Cut: discard every choice point created since the call that selected the current
clause (`to` is the choice-stack height recorded at that call). -/
-- @tg: implements:: [[openspec:elpi-core-engine#Cut]]
def cut {σ : Type} (M : Machine σ) (to : Nat) : Machine σ :=
  { M with choices := M.choices.shrink to }

/-- Rename a clause term for use at depth `d` (see `Term.renameCVars`). -/
def rename (vars : Array Term) (d : Nat) (t : Term) : Term := Term.renameCVars vars d t

def argsOf : Term → Array Term
  | .app _ as => as
  | _ => #[]

/-- Give every still-unbound clause variable a fresh unification variable at depth `d`. -/
def fillVars (s : Store) (vars : Array (Option Term)) (d : Nat) : Store × Array Term := Id.run do
  let mut s := s
  let mut out : Array Term := Array.mkEmpty vars.size
  for v in vars do
    match v with
    | some t => out := out.push t
    | none =>
      let (u, s') := s.fresh d
      s := s'
      out := out.push (.uvar u #[])
  return (s, out)

/-- Match a clause-head term `h` against the goal term `g` at depth `d`. The first occurrence
of a clause variable is bound directly to the goal's subterm, so no unification variable is
created and no scope check walks the (possibly huge) subterm; every other case falls back to
general unification of the instantiated head. `gen` is the general unifier of the argument.
The store is always returned; after a failure it holds partial bindings for the caller to undo. -/
partial def hmatch (gen : Store → Term → Term → Store × Bool) (st : Store)
    (vars : Array (Option Term)) (h g : Term) (d : Nat) :
    Store × Array (Option Term) × Bool :=
  match h with
  | .cvar i args =>
    if args.isEmpty then
      match vars[i]! with
      | none => (st, vars.set! i (some g), true)
      | some t => let (st', ok) := gen st t g; (st', vars, ok)
    else fallback gen st vars h g d
  | .const c =>
    match st.deref g d with
    | .const c' => if c == c' then (st, vars, true) else clash gen st vars h g d
    | .uvar .. | .lam _ => fallback gen st vars h g d
    | _ => clash gen st vars h g d
  | .app (.const c) hargs =>
    match st.deref g d with
    | .app (.const c') gargs =>
      if c == c' && hargs.size == gargs.size then
        matchArgs gen st vars hargs gargs d 0
      else clash gen st vars h g d
    | .uvar .. | .lam _ => fallback gen st vars h g d
    | _ => clash gen st vars h g d
  | _ => fallback gen st vars h g d
where
  matchArgs (gen : Store → Term → Term → Store × Bool) (st : Store) (vars : Array (Option Term))
      (hargs gargs : Array Term) (d : Nat) (i : Nat) : Store × Array (Option Term) × Bool :=
    if h : i < hargs.size then
      match hmatch gen st vars hargs[i] gargs[i]! d with
      | (st', vars', true) => matchArgs gen st' vars' hargs gargs d (i + 1)
      | r => r
    else (st, vars, true)
  fallback (gen : Store → Term → Term → Store × Bool) (st : Store) (vars : Array (Option Term))
      (h g : Term) (d : Nat) : Store × Array (Option Term) × Bool :=
    let (st1, vs) := fillVars st vars d
    let (st2, ok) := gen st1 (Term.renameCVars vs d h) g
    (st2, vs.map some, ok)
  -- a rigid clash fails outright unless hooks may interpret the constants
  clash (gen : Store → Term → Term → Store × Bool) (st : Store) (vars : Array (Option Term))
      (h g : Term) (d : Nat) : Store × Array (Option Term) × Bool :=
    if st.hooks.isEmpty then (st, vars, false) else fallback gen st vars h g d

/-- Match head arguments `i…` of a clause against the call's, threading the store and the clause
variables. Explicit recursion rather than a `for` loop with `return`: do-notation would keep
the previous store in the loop's result state, a second reference that forces every update to
copy the store's arrays. -/
partial def matchArgs (modes : Option (Array Mode)) (boundary d : Nat) (hargs gargs : Array Term)
    (i : Nat) (st : Store) (vars : Array (Option Term)) : Store × Array (Option Term) × Bool :=
  if h : i < hargs.size then
    let isIn : Bool := match modes with | some ms => (ms.getD i Mode.o) == Mode.i | none => false
    let gen : Store → Term → Term → Store × Bool :=
      if isIn then fun s a b => unifyMatchRaw s boundary a b d else fun s a b => unifyRaw s a b d
    match hmatch gen st vars hargs[i] gargs[i]! d with
    | (st', vars', true) => matchArgs modes boundary d hargs gargs (i + 1) st' vars'
    | r => r
  else (st, vars, true)

/-- Instantiate a static clause for the call arguments `gargs` at depth `d`: match the head
argument by argument (match mode on input positions), then instantiate the body. The store
is returned in every case; `none` means the head does not match. -/
def matchClause (c : Clause) (modes : Option (Array Mode)) (s : Store) (boundary : Nat)
    (gargs : Array Term) (d : Nat) : Store × Option Term :=
  let hargs := argsOf c.head
  if hargs.size != gargs.size then (s, none) else
  match matchArgs modes boundary d hargs gargs 0 s (Array.replicate c.nvars none) with
  | (st, _, false) => (st, none)
  | (st, vars, true) =>
    match c.body with
    | .const k =>
      if k == cTrue then (st, some c.body)
      else let (st', vs) := fillVars st vars d; (st', some (Term.renameCVars vs d c.body))
    | _ => let (st', vs) := fillVars st vars d; (st', some (Term.renameCVars vs d c.body))

/-- Peel `pi` quantifiers and `:-` off a hypothetical clause used at depth `d`. -/
partial def instLocal (lc : LocalClause) (s : Store) (d : Nat) : Store × Term × Term :=
  let t := lc.term.shiftUp lc.depth (d - lc.depth)
  go t s
where
  go (t : Term) (s : Store) : Store × Term × Term :=
    match s.deref t d with
    | .app (.const c) #[.lam b] =>
      if c == cPi then
        let (u, s') := s.fresh d
        go (Term.instantiate b d (.uvar u #[])) s'
      else (s, t, .const cTrue)
    | .app (.const c) #[h, b] =>
      if c == cNeck then (s, h, b) else (s, t, .const cTrue)
    | t' => (s, t', .const cTrue)

/-- Head constant of a hypothetical clause, if syntactically visible. -/
partial def localHead (s : Store) (t : Term) (d : Nat) : Option ConstId :=
  match s.deref t d with
  | .app (.const c) #[.lam b] => if c == cPi then localHead s b (d + 1) else some c
  | .app (.const c) #[h, _] => if c == cNeck then localHead s h d else some c
  | .app (.const c) _ => some c
  | .const c => some c
  | _ => none

/-- First-argument key of a hypothetical clause stored at depth `base`: an eigenvariable (a
level below `base`) is rigid, while the clause's own `pi`-bound names are variables. -/
partial def localKey (s : Store) (base : Nat) (t : Term) (d : Nat) : Key :=
  match s.deref t d with
  | .app (.const c) #[.lam b] => if c == cPi then localKey s base b (d + 1) else .flex
  | .app (.const c) #[h, _] => if c == cNeck then localKey s base h d else firstArgKey s base t d
  | t' => firstArgKey s base t' d
where
  firstArgKey (s : Store) (base : Nat) (t : Term) (d : Nat) : Key :=
    match s.deref t d with
    | .app _ as => if h : 0 < as.size then
        (match s.deref as[0] d with
         | .bound l => if l < base then .bound l else .flex
         | a => Key.ofTerm a)
      else .flex
    | _ => .flex

/-- A hypothetical clause with its head and first-argument key worked out now. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Hypothesis indexing]]
def mkLocal (s : Store) (t : Term) (d : Nat) : LocalClause :=
  match localHead s t d with
  | some h => { term := t, depth := d, head := some h, key := localKey s d t d }
  | none => { term := t, depth := d }

/-- Split a clause set (`,`-conjunction or list) into hypothetical clauses. -/
partial def toLocals (s : Store) (t : Term) (d : Nat) : List LocalClause :=
  match s.deref t d with
  | .app (.const c) #[a, b] =>
    if c == cConj || c == cCons then toLocals s a d ++ toLocals s b d
    else [mkLocal s t d]
  | .const c => if c == cTrue || c == cNil then [] else [mkLocal s t d]
  | _ => [mkLocal s t d]

/-- Unify head arguments (from position `i`) with goal arguments, in match mode for input
positions. The store is returned in every case, with partial bindings after a failure. -/
partial def unifyHeadFrom (modes : Option (Array Mode)) (boundary : Nat) (hargs gargs : Array Term)
    (d : Nat) (i : Nat) (s : Store) : Store × Bool :=
  if h : i < hargs.size then
    let isIn : Bool := match modes with | some ms => (ms.getD i Mode.o) == Mode.i | none => false
    let (s', ok) := if isIn then unifyMatchRaw s boundary hargs[i] gargs[i]! d
                    else unifyRaw s hargs[i] gargs[i]! d
    if ok then unifyHeadFrom modes boundary hargs gargs d (i + 1) s' else (s', false)
  else (s, true)

def unifyHead (modes : Option (Array Mode)) (s : Store) (boundary : Nat)
    (hargs gargs : Array Term) (d : Nat) : Store × Bool :=
  if hargs.size != gargs.size then (s, false)
  else unifyHeadFrom modes boundary hargs gargs d 0 s

/-- Copy a term out of a finished sub-run: assigned variables are replaced by their
values, unassigned ones by fresh variables of the outer store. -/
partial def copyOut (src : Store) (t : Term) (d : Nat) :
    StateM (Store × Std.HashMap Nat UVarId) Term := do
  match src.deref t d with
  | .uvar u as =>
    let as' ← as.mapM (copyOut src · d)
    let (s, mp) ← get
    match mp[u.idx]? with
    | some v => return .uvar v as'
    | none =>
      let (v, s') := s.fresh d
      set (s', mp.insert u.idx v)
      return .uvar v as'
  | .app h as => return .app (← copyOut src h d) (← as.mapM (copyOut src · d))
  | .lam b => return .lam (← copyOut src b (d + 1))
  | t => return t

end Machine

open Machine

/-- Frames for goals pushed by a handler or a rule body, in the context of `f`. -/
def goalFrames (f : Frame) (cutTo : Nat) (goals : List Term) : List Frame :=
  goals.map fun g => { goal := g, depth := f.depth, locals := f.locals, cutTo }

/-- The view of the store a native handler is given. -/
def hstoreOf (name : String) (h : ConstraintHandler) (s : Store) (d : Nat) : HStore :=
  { owned := s.cstore.toList.filter (·.owner == some name)
    state := (s.cstore.handlerState.find? name).getD h.init
    deref := fun t => s.deref t d }

/-- Apply a handler's answer: `none` means the handler failed. `newC` is the constraint
being added (for `onAdd`); the result is the new store and the goals to push. -/
def applyHandler (name : String) (s : Store) (f : Frame) (cutTo : Nat) (res : HandlerResult)
    (newC : Option Constraint) : Option (Store × List Frame) :=
  let setState (st? : Option Dynamic) (s : Store) : Store :=
    match st? with
    | some d => { s with cstore := { s.cstore with handlerState := s.cstore.handlerState.insert name d } }
    | none => s
  let addNew (s : Store) : Store :=
    match newC with
    | some c => { s with cstore := (s.cstore.add { c with owner := some name }).2 }
    | none => s
  match res with
  | .fail => none
  | .keep st? => some (setState st? (addNew s), [])
  | .propagate goals st? => some (setState st? (addNew s), goalFrames f cutTo goals)
  | .simplify keep st? =>
    let cs := s.cstore.toList.filter (·.owner == some name) |>.foldl (fun cs c => cs.remove c.id) s.cstore
    let cs := keep.foldl (fun cs c => (cs.add { c with owner := some name }).2) cs
    some (setState st? { s with cstore := cs }, [])

/-- The goal list after selecting a clause: its body (unless it is `true`) on top of the
continuation. -/
def bodyGoals (goals : List Frame) (b : Term) (d : Nat) (call : Frame) (barrier : Nat) : List Frame :=
  match b with
  | .const c => if c == cTrue then goals
                else { goal := b, depth := d, locals := call.locals, cutTo := barrier, ldepth := call.ldepth } :: goals
  | _ => { goal := b, depth := d, locals := call.locals, cutTo := barrier, ldepth := call.ldepth } :: goals

/-- The outcome of looking through the candidate clauses of a call for one whose head matches. -/
structure Pick where
  /-- The store after the match (a failed search leaves the store as it was). -/
  store : Store
  /-- The instantiated body of the matching clause; `none` when no candidate matched. -/
  body : Option Term := none
  /-- Position in `cands` of the matching clause. -/
  index : Nat := 0
  /-- Checkpoint taken just before the matching attempt. -/
  cp : Store := {}
  deriving Inhabited

/-- Try `cands[i:]` in order. This is pure code on purpose: the store is consumed here and handed
back, so its arrays are updated in place (monadic code would capture it in continuations). -/
partial def pickClause (cands : Array Cand) (modes : Option (Array Mode)) (boundary d : Nat)
    (gargs : Array Term) (s : Store) (i : Nat) : Pick :=
  if i < cands.size then
    let cp := s.checkpoint
    let (s1, r) : Store × Option Term :=
      match cands[i]! with
      | .static c => matchClause c modes s.track boundary gargs d
      | .local lc =>
        let (s2, h, b) := instLocal lc s.track d
        let (s3, ok) := unifyHead modes s2 boundary (argsOf h) gargs d
        (s3, if ok then some b else none)
    match r with
    | none => pickClause cands modes boundary d gargs (s1.undo cp) (i + 1)
    | some b => { store := s1, body := some b, index := i, cp }
  else { store := s }

/-- Unify a builtin's answer tuple with the call arguments, from position `j`. -/
def unifyTuple (s : Store) (tuple gargs : Array Term) (d : Nat) (j : Nat) : Store × Bool :=
  if h : j < tuple.size then
    let (s', ok) := unifyRaw s tuple[j] gargs[j]! d
    if ok then unifyTuple s' tuple gargs d (j + 1) else (s', false)
  else (s, true)

/-- The outcome of looking through a builtin's answers for one that unifies with the call. -/
inductive PickT where
  | none (s : Store)
  | bad
  | some (s : Store) (cp : Store) (next : LazyList (Array Term))
  deriving Inhabited

partial def pickTuple (gargs : Array Term) (d : Nat) (s : Store) : LazyList (Array Term) → PickT
  | .nil => .none s
  | .cons tuple tl =>
    if tuple.size != gargs.size then .bad else
    let cp := s.checkpoint
    let (s1, ok) := unifyTuple s.track tuple gargs d 0
    if ok then .some s1 cp tl.get else pickTuple gargs d (s1.undo cp) tl.get

mutual
/-- Backtrack to the most recent choice point and resume its alternative. `cur` is the store
the failed branch ended with; the choice point's checkpoint undoes it. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Depth-first search order]]
partial def backtrack {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (cur : Store) : m (SR σ) := do
  let some cp := M.choices.back? | return .done (.exhausted M.cutoff M.fuel)
  let choices := M.choices.pop
  Backtrackable.restore cp.host
  let s := cur.undo cp.store
  let M' : Machine σ := { M with choices, goals := cp.goals, resume := false }
  match cp.alt with
  | .frame f => return .cont { M' with goals := f :: cp.goals } s
  | .clauses call cands next => tryClauses env M' s call cands next
  | .stream call rest => tryStream env M' s call rest

/-- Try the candidate clauses `cands[next:]` for `call`. `M.goals` is the continuation. -/
partial def tryClauses {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (s : Store) (call : Frame) (cands : Array Cand) (next : Nat) :
    m (SR σ) := do
  let d := call.depth
  let goal := s.deref call.goal d
  let gargs := argsOf goal
  let pred : Option ConstId := match goal with
    | .app (.const c) _ => some c | .const c => some c | _ => none
  let modes := pred.bind fun c => env.modes[c.idx]?
  let p := pickClause cands modes s.nextVar d gargs s next
  match p.body with
  | none => backtrack env M p.store
  | some b =>
    let barrier := M.choices.size
    -- push an alternative if further candidates remain
    if p.index + 1 < cands.size then
      let host ← Backtrackable.save
      let choices := M.choices.push
        { goals := M.goals, store := p.cp, host, alt := .clauses call cands (p.index + 1) }
      return .cont { M with goals := bodyGoals M.goals b d call barrier, choices } p.store
    else
      return .cont { M with goals := bodyGoals M.goals b d call barrier } (p.store.settle p.cp)

/-- Try the next alternative of a builtin's stream. -/
partial def tryStream {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (s : Store) (call : Frame) (rest : LazyList (Array Term)) :
    m (SR σ) := do
  let d := call.depth
  let gargs := argsOf (s.deref call.goal d)
  match pickTuple gargs d s rest with
  | .none s' => backtrack env M s'
  | .bad => return .done (.error (.runtime "builtin returned a tuple of the wrong size"))
  | .some s1 cp next =>
    match next with
    | .nil => return .cont M (s1.settle cp)
    | _ =>
      let host ← Backtrackable.save
      let choices := M.choices.push { goals := M.goals, store := cp, host, alt := .stream call next }
      return .cont { M with choices } s1

/-- Run a rule guard in a nested machine with every store variable frozen. `none` means the
guard failed (or tried to bind a frozen variable). -/
partial def runGuard {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (c : Constraint) (mt : CHRMatch) (g : Term) :
    m (Except (Step σ) (Option Store)) := do
  let gt := Term.renameCVars mt.vars c.depth g
  let st := { mt.store with protect := mt.store.nextVar }
  let sub : Machine σ :=
    { goals := [{ goal := gt, depth := c.depth, locals := c.locals, cutTo := 0 }],
      store := st, fuel := M.fuel }
  let host ← Backtrackable.save
  let r ← runLoop env sub
  Backtrackable.restore host
  match r with
  | .yield sol _ => return .ok (some { sol.store with protect := 0 })
  | .exhausted _ _ => return .ok none
  | .outOfFuel => return .error .outOfFuel
  | .error e => return .error (.error e)

/-- Activate a newly added constraint: try the rules of every block over its predicate, in
source order, with the constraint at each head position; fire the first rule whose heads
match and whose guard succeeds (kept constraints may fire further rules). Bodies are
pushed as goals, in firing order. -/
-- @tg: implements:: [[openspec:elpi-constraints#CHR rules]]
partial def activate {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M0 : Machine σ) (f : Frame) (c : Constraint) : m (Except (Step σ) (Machine σ)) := do
  let some pred := c.pred | return .ok M0
  let ts := some cTurn
  let mut M := M0
  let mut bodies : Array Frame := #[]
  let mut alive := true
  let mut fired : Array (Nat × Nat × Array Nat) := #[]
  let mut bi := 0
  for b in env.blocks do
    bi := bi + 1
    unless b.preds.contains pred do continue
    let mut ri := 0
    for r in b.rules do
      ri := ri + 1
      let heads := r.kept ++ r.removed
      for pos in [0:heads.size] do
        if !alive then break
        unless headPred ts heads[pos]! == some pred do continue
        -- keep firing this (rule, position) while new matches pass their guard
        let mut again := true
        while again && alive do
          again := false
          for mt in matchRule ts r M.store c pos do
            if !(mt.ids.all fun id => (M.store.cstore.find? id).isSome) then continue
            if fired.contains (bi, ri, mt.ids) then continue
            let ok : Except (Step σ) (Option Store) ←
              match r.guard with
              | none => pure (.ok (some mt.store))
              | some g => runGuard env M c mt g
            match ok with
            | .error e => return .error e
            | .ok none => continue
            | .ok (some st) =>
              fired := fired.push (bi, ri, mt.ids)
              let rem := mt.ids.extract r.kept.size mt.ids.size
              let st := rem.foldl (fun (st : Store) id => { st with cstore := st.cstore.remove id }) st
              if rem.contains c.id then alive := false
              M := { M with store := st }
              match r.body with
              | some body =>
                bodies := bodies.push
                  { goal := Term.renameCVars mt.vars c.depth body, depth := c.depth,
                    locals := c.locals, cutTo := M.choices.size }
              | none => pure ()
              again := true
              break
  return .ok { M with goals := bodies.toList ++ M.goals }

/-- Resume the constraints woken by assignments, before the next goal runs. -/
-- @tg: implements:: [[openspec:elpi-constraints#Delayed goals]]
partial def drainWake {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (s : Store) : m (SR σ) := do
  let q := s.wakeQueue.reverse
  let mut st := { s with wakeQueue := [] }
  let mut frames : Array Frame := #[]
  let mut seen : List (String × UVarId) := []
  for (id, u) in q do
    match st.cstore.find? id with
    | none => pure ()
    | some c =>
      match c.owner with
      | none =>
        st := { st with cstore := st.cstore.remove id }
        frames := frames.push
          { goal := c.goal, depth := c.depth, locals := c.locals, cutTo := M.choices.size }
      | some name =>
        unless seen.contains (name, u) do
          seen := (name, u) :: seen
          match env.handlers.toList.find? (·.2.1 == name) with
          | none => pure ()
          | some (_, (_, h)) =>
            let fr : Frame := { goal := c.goal, depth := c.depth, locals := c.locals, cutTo := M.choices.size }
            match applyHandler name st fr M.choices.size (h.onWake u (hstoreOf name h st c.depth)) none with
            | none => return (← backtrack env M st)
            | some (st', fs) =>
              st := st'
              frames := frames ++ fs.toArray
  return .cont { M with goals := frames.toList ++ M.goals } st

/-- One machine step: process the top goal. The store `s` is the machine's own and is passed
on to whichever step consumes it. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Hereditary Harrop goals]]
partial def stepM {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (s : Store) : m (SR σ) := do
  if M.resume then
    return (← backtrack env { M with resume := false } s)
  if !s.wakeQueue.isEmpty then
    return (← drainWake env M s)
  match M.goals with
  | [] =>
    -- solution: whatever is still suspended is reported with it
    return .done (.yield { store := s, constraints := s.cstore.toList } { M with store := s, resume := true })
  | f :: rest =>
    if M.fuel == 0 then return .done .outOfFuel
    let M := { M with fuel := M.fuel - 1 }
    let d := f.depth
    let goal := s.deref f.goal d
    match goal with
    | .const c =>
      if c == cTrue then return .cont { M with goals := rest } s
      else if c == cFail then backtrack env { M with goals := rest } s
      else if c == cCut then
        return .cont (cut { M with goals := rest } f.cutTo) s
      else callPred env M s f c #[] rest
    | .app (.const c) args =>
      if c == cConj && args.size == 2 then
        return .cont { M with goals := { f with goal := args[0]! } :: { f with goal := args[1]! } :: rest } s
      else if c == cOr && args.size == 2 then
        let host ← Backtrackable.save
        let cp : ChoicePoint σ :=
          { goals := rest, store := s.checkpoint, host, alt := .frame { f with goal := args[1]! } }
        return .cont { M with goals := { f with goal := args[0]! } :: rest,
                              choices := M.choices.push cp } s.track
      else if c == cImpl && args.size == 2 then
        let ls := toLocals s args[0]! d
        return .cont { M with goals := { f with goal := args[1]!, locals := ls ++ f.locals } :: rest } s
      else if c == cPi && args.size == 1 then
        let g' := match s.deref args[0]! d with
          | .lam b => b
          | other => Term.applyAt (other.shiftUp d 1) #[.bound d] (d + 1)
        return .cont { M with goals := { f with goal := g', depth := d + 1 } :: rest } s
      else if c == cSigma && args.size == 1 then
        let (u, s') := s.fresh d
        let v := Term.uvar u #[]
        let g' := match s'.deref args[0]! d with
          | .lam b => Term.instantiate b d v
          | other => Term.applyAt other #[v] d
        return .cont { M with goals := { f with goal := g' } :: rest } s'
      else if c == cEq && args.size == 2 then
        let cp := s.checkpoint
        let (s', ok) := unifyRaw s.track args[0]! args[1]! d
        if ok then return .cont { M with goals := rest } (s'.settle cp)
        else backtrack env { M with goals := rest } s'
      else if c == cDeclare && args.size == 2 then
        -- suspend a goal on the variables of the key list
        let keys := Unify.collectUVars s args[1]! d
        let pred := Unify.headConst (s.deref args[0]! d)
        let cn : Constraint :=
          { id := 0, goal := args[0]!, keys, depth := d, locals := f.locals, pred }
        match pred.bind (fun p => env.handlers[p.idx]?) with
        | some (name, h) =>
          let res := h.onAdd cn (hstoreOf name h s d)
          match applyHandler name s f M.choices.size res (some cn) with
          | none => backtrack env { M with goals := rest } s
          | some (st, fs) => return .cont { M with goals := fs ++ rest } st
        | none =>
          let (c', cs) := s.cstore.add cn
          let M1 : Machine σ := { M with store := { s with cstore := cs }, goals := rest }
          match ← activate env M1 f c' with
          | .ok M2 =>
            let (s2, M2) := M2.takeStore
            return .cont M2 s2
          | .error r => return .done r
      else if c == cNot && args.size == 1 then
        -- not G  ≡  (G, !, fail) ; true   with the cut local to this construct
        let host ← Backtrackable.save
        let before := M.choices.size
        let cp : ChoicePoint σ :=
          { goals := rest, store := s.checkpoint, host, alt := .frame { f with goal := .const cTrue } }
        let g1 : Frame := { f with goal := args[0]!, cutTo := before + 1 }
        let g2 : Frame := { f with goal := .const cCut, cutTo := before }
        let g3 : Frame := { f with goal := .const cFail }
        return .cont { M with choices := M.choices.push cp, goals := g1 :: g2 :: g3 :: rest } s.track
      else if c == cFindall && args.size == 2 then
        -- run a nested machine to completion, collecting instances of the goal; each
        -- solution is copied out at once, so no solution keeps a copy of the store alive
        let host ← Backtrackable.save
        let nv0 := s.nextVar
        let sub : Machine σ :=
          { goals := [{ f with goal := args[0]!, cutTo := 0 }], store := s, fuel := M.fuel }
        let mut cur := sub
        let mut outer := s
        let mut mp : Std.HashMap Nat UVarId := {}
        let mut items : Array Term := #[]
        let mut err : Option (Step σ) := none
        let mut fuelLeft := M.fuel
        repeat
          match ← runLoop env cur with
          | .yield sol resume =>
            -- variables created inside the sub-run differ from one solution to the next
            let (t, (o', mp')) := (copyOut sol.store args[0]! d).run (outer, mp)
            outer := o'
            mp := mp'.filter fun k _ => k < nv0
            items := items.push t
            fuelLeft := resume.fuel
            cur := resume
          | .exhausted _ _ => break
          | .outOfFuel => err := some .outOfFuel; break
          | .error e => err := some (.error e); break
        Backtrackable.restore host
        match err with
        | some e => return .done e
        | none =>
          let lst := items.foldr (fun x acc => Term.app (.const cCons) #[x, acc]) (.const cNil)
          match unify outer args[1]! lst d with
          | some s'' => return .cont { M with goals := rest, fuel := fuelLeft } s''
          | none => backtrack env { M with goals := rest } s
      else callPred env M s f c args rest
    | .uvar .. => return .done (.error (.runtime "uninstantiated goal"))
    | _ => return .done (.error (.runtime "ill-formed goal"))

partial def callPred {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ] (env : Env m)
    (M : Machine σ) (s : Store) (f : Frame) (c : ConstId) (args : Array Term)
    (rest : List Frame) : m (SR σ) := do
    let d := f.depth
    let M := { M with goals := rest }
    match env.builtins[c.idx]? with
    | some b =>
      let dargs := args.map (s.deref · d)
      match ← b.run { syms := env.syms, store := s, depth := d } dargs with
      | .fail => backtrack env M s
      | .error msg => return .done (.error (.runtime msg))
      | .alts s' l => tryStream env M s' f l
    | none =>
      -- normalise the arguments' heads once: later steps then find them already dereferenced
      let args := args.map (s.deref · d)
      let key := if h : 0 < args.size then Key.ofTerm args[0] else .flex
      let mut cands : Array Cand := #[]
      for lc in f.locals do
        let ok :=
          match lc.head with
          | some h => h == c && lc.key.compatible key
          | none => localHead s lc.term lc.depth == some c &&
                    (localKey s lc.depth lc.term lc.depth).compatible key
        if ok then cands := cands.push (.local lc)
      match env.db.preds.find? c with
      | some db =>
        for i in db.candidates key do
          cands := cands.push (.static db.clauses[i]!)
      | none => pure ()
      -- LF goals go one derivation level deeper; the strategy's bound prunes them
      let isLF := env.lfPreds.contains c.idx
      let nd := if isLF then f.ldepth + 1 else f.ldepth
      let pruned := match env.bound with | some b => isLF && nd > b | none => false
      if pruned then
        backtrack env { M with cutoff := true } s
      else if cands.isEmpty then
        -- unknown predicate without clauses simply fails
        backtrack env M s
      else
        let call : Frame := { f with goal := (if args.isEmpty then .const c else .app (.const c) args),
                                     cutTo := M.choices.size, ldepth := nd }
        tryClauses env M s call cands 0

/-- Run steps until the machine yields, is exhausted, runs out of fuel or fails. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Abstract machine]]
partial def runLoop {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) : m (Step σ) := do
  let (s, M) := M.takeStore
  runLoopS env M s

/-- `runLoop` with the store held beside the machine. -/
partial def runLoopS {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (s : Store) : m (Step σ) := do
  match ← stepM env M s with
  | .cont M' s' => runLoopS env M' s'
  | .done r => return r

end

end Elpi
