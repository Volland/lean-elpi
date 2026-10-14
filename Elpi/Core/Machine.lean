import Std.Data.HashMap
import Elpi.Core.Store
import Elpi.Core.Unify
import Elpi.Core.Index
import Elpi.Core.Builtins

/-!
# Abstract machine

An explicit first-order machine for hereditary Harrop goals: the goal stack, the choice
stack and the cut barriers are heap data, so ELPI recursion depth is not bounded by the
native stack. Choice points keep the persistent `Store` and a host-monad snapshot.
-/

-- @lat: [[components#Abstract machine]]

namespace Elpi

/-- A clause added by `=>`: a clause term and the depth it was added at. -/
structure LocalClause where
  term : Term
  depth : Nat
  deriving Inhabited

/-- Hypothetical clauses, newest group first. -/
abbrev Locals := List LocalClause

/-- A goal to solve, closed over the depth and local program it runs under. -/
structure Frame where
  goal : Term
  depth : Nat
  locals : Locals
  /-- Choice-stack height to cut back to (cut barrier). -/
  cutTo : Nat
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
  deriving Inhabited

/-- Static environment of a run. -/
structure Env (m : Type → Type) where
  syms : Symbols
  db : Database
  modes : Std.HashMap Nat (Array Mode)
  builtins : Std.HashMap Nat (Builtin m)

/-- A raw solution: the final store and the residual suspended problems. -/
structure RawSolution where
  store : Store
  residual : List DelayedProblem := []
  deriving Inhabited

inductive Step (σ : Type) where
  | yield (s : RawSolution) (resume : Machine σ)
  | exhausted
  | outOfFuel
  | error (e : ElpiError)

/-- Result of one machine step. -/
inductive SR (σ : Type) where
  | cont (M : Machine σ)
  | done (r : Step σ)

instance {σ : Type} : Inhabited (SR σ) := ⟨.done .exhausted⟩
instance {σ : Type} : Inhabited (Step σ) := ⟨.exhausted⟩

namespace Machine

/-- Cut: discard every choice point created since the call that selected the current
clause (`to` is the choice-stack height recorded at that call). -/
-- @tg: implements:: [[openspec:elpi-core-engine#Cut]]
def cut {σ : Type} (M : Machine σ) (to : Nat) : Machine σ :=
  { M with choices := M.choices.shrink to }

/-- Rename a clause term for use at depth `d`: clause variables become fresh unification
variables, bound levels (all internal binders of a top-level clause) move to `d`. -/
partial def rename (vars : Array Term) (d : Nat) : Term → Term
  | .bound l => .bound (l + d)
  | .cvar i args =>
    let args' := args.map (rename vars d)
    Term.mkApp vars[i]! args'
  | .app h as => .app (rename vars d h) (as.map (rename vars d))
  | .lam b => .lam (rename vars d b)
  | .uvar u as => .uvar u (as.map (rename vars d))
  | t => t

/-- Instantiate a static clause at depth `d`. -/
def instClause (c : Clause) (s : Store) (d : Nat) : Store × Term × Term := Id.run do
  let mut s := s
  let mut vars : Array Term := Array.mkEmpty c.nvars
  for _ in [0:c.nvars] do
    let (u, s') := s.fresh d
    s := s'
    vars := vars.push (.uvar u #[])
  return (s, rename vars d c.head, rename vars d c.body)

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

/-- Split a clause set (`,`-conjunction or list) into hypothetical clauses. -/
partial def toLocals (s : Store) (t : Term) (d : Nat) : List LocalClause :=
  match s.deref t d with
  | .app (.const c) #[a, b] =>
    if c == cConj || c == cCons then toLocals s a d ++ toLocals s b d
    else [{ term := t, depth := d }]
  | .const c => if c == cTrue || c == cNil then [] else [{ term := t, depth := d }]
  | _ => [{ term := t, depth := d }]

def argsOf : Term → Array Term
  | .app _ as => as
  | _ => #[]

/-- Unify head arguments with goal arguments, in match mode for input positions. -/
def unifyHead (modes : Option (Array Mode)) (s : Store) (boundary : Nat)
    (hargs gargs : Array Term) (d : Nat) : Option Store := Id.run do
  if hargs.size != gargs.size then return none
  let mut s := s
  for i in [0:hargs.size] do
    let isIn : Bool := match modes with | some ms => (ms.getD i Mode.o) == Mode.i | none => false
    let r := if isIn then unifyMatch s boundary hargs[i]! gargs[i]! d
             else unify s hargs[i]! gargs[i]! d
    match r with
    | some s' => s := s'
    | none => return none
  return some s

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

mutual
/-- Backtrack to the most recent choice point and resume its alternative. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Depth-first search order]]
partial def backtrack {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) : m (SR σ) := do
  let some cp := M.choices.back? | return .done .exhausted
  let choices := M.choices.pop
  Backtrackable.restore cp.host
  let M' : Machine σ := { M with choices, store := cp.store, goals := cp.goals, resume := false }
  match cp.alt with
  | .frame f => return .cont { M' with goals := f :: cp.goals }
  | .clauses call cands next => tryClauses env M' call cands next
  | .stream call rest => tryStream env M' call rest

/-- Try the candidate clauses `cands[next:]` for `call`. `M.goals` is the continuation. -/
partial def tryClauses {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (call : Frame) (cands : Array Cand) (next : Nat) :
    m (SR σ) := do
  let d := call.depth
  let goal := M.store.deref call.goal d
  let gargs := argsOf goal
  let pred : Option ConstId := match goal with
    | .app (.const c) _ => some c | .const c => some c | _ => none
  let modes := pred.bind fun c => env.modes[c.idx]?
  let mut i := next
  while i < cands.size do
    let cand := cands[i]!
    let (s1, h, b) := match cand with
      | .static c => instClause c M.store d
      | .local lc => instLocal lc M.store d
    let r := unifyHead modes s1 M.store.nextVar (argsOf h) gargs d
    match r with
    | none => i := i + 1
    | some s2 =>
      let barrier := M.choices.size
      -- push an alternative if further candidates remain
      let mut choices := M.choices
      if i + 1 < cands.size then
        let host ← Backtrackable.save
        choices := choices.push
          { goals := M.goals, store := M.store, host, alt := .clauses call cands (i + 1) }
      let goals :=
        match b with
        | .const c => if c == cTrue then M.goals
                      else { goal := b, depth := d, locals := call.locals, cutTo := barrier } :: M.goals
        | _ => { goal := b, depth := d, locals := call.locals, cutTo := barrier } :: M.goals
      return .cont { M with goals, choices, store := s2, fuel := M.fuel }
  backtrack env M

/-- Try the next alternative of a builtin's stream. -/
partial def tryStream {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) (call : Frame) (rest : LazyList (Array Term)) :
    m (SR σ) := do
  let d := call.depth
  let gargs := argsOf (M.store.deref call.goal d)
  let mut cur := rest
  repeat
    match cur with
    | .nil => return (← backtrack env M)
    | .cons tuple tl =>
      let next := tl.get
      let mut s := some M.store
      if tuple.size != gargs.size then
        return .done (.error (.runtime "builtin returned a tuple of the wrong size"))
      for j in [0:tuple.size] do
        match s with
        | some st => s := unify st tuple[j]! gargs[j]! d
        | none => break
      match s with
      | none => cur := next
      | some s2 =>
        let mut choices := M.choices
        match next with
        | .nil => pure ()
        | _ =>
          let host ← Backtrackable.save
          choices := choices.push
            { goals := M.goals, store := M.store, host, alt := .stream call next }
        return .cont { M with choices, store := s2 }
  return (← backtrack env M)

/-- One machine step: process the top goal. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Hereditary Harrop goals]]
partial def stepM {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) : m (SR σ) := do
  if M.resume then
    return (← backtrack env { M with resume := false })
  match M.goals with
  | [] =>
    -- solution: re-examine suspended problems
    match resolveDelayed M.store with
    | none => backtrack env M
    | some (s, residual) =>
      return .done (.yield { store := s, residual } { M with store := s, resume := true })
  | f :: rest =>
    if M.fuel == 0 then return .done .outOfFuel
    let M := { M with fuel := M.fuel - 1 }
    let d := f.depth
    let s := M.store
    let goal := s.deref f.goal d
    let withRest (g : Frame) : Machine σ := { M with goals := g :: rest }
    match goal with
    | .const c =>
      if c == cTrue then return .cont { M with goals := rest }
      else if c == cFail then backtrack env { M with goals := rest }
      else if c == cCut then
        return .cont (cut { M with goals := rest } f.cutTo)
      else callPred env M f c #[] rest
    | .app (.const c) args =>
      if c == cConj && args.size == 2 then
        return .cont { M with goals := { f with goal := args[0]! } :: { f with goal := args[1]! } :: rest }
      else if c == cOr && args.size == 2 then
        let host ← Backtrackable.save
        let cp : ChoicePoint σ :=
          { goals := rest, store := s, host, alt := .frame { f with goal := args[1]! } }
        return .cont { M with goals := { f with goal := args[0]! } :: rest,
                              choices := M.choices.push cp }
      else if c == cImpl && args.size == 2 then
        let ls := toLocals s args[0]! d
        return .cont (withRest { f with goal := args[1]!, locals := ls ++ f.locals })
      else if c == cPi && args.size == 1 then
        let g' := match s.deref args[0]! d with
          | .lam b => b
          | other => Term.applyAt (other.shiftUp d 1) #[.bound d] (d + 1)
        return .cont (withRest { f with goal := g', depth := d + 1 })
      else if c == cSigma && args.size == 1 then
        let (u, s') := s.fresh d
        let v := Term.uvar u #[]
        let g' := match s.deref args[0]! d with
          | .lam b => Term.instantiate b d v
          | other => Term.applyAt other #[v] d
        return .cont { M with store := s', goals := { f with goal := g' } :: rest }
      else if c == cEq && args.size == 2 then
        match unify s args[0]! args[1]! d with
        | some s' => return .cont { M with store := s', goals := rest }
        | none => backtrack env { M with goals := rest }
      else if c == cNot && args.size == 1 then
        -- not G  ≡  (G, !, fail) ; true   with the cut local to this construct
        let host ← Backtrackable.save
        let before := M.choices.size
        let cp : ChoicePoint σ :=
          { goals := rest, store := s, host, alt := .frame { f with goal := .const cTrue } }
        let g1 : Frame := { f with goal := args[0]!, cutTo := before + 1 }
        let g2 : Frame := { f with goal := .const cCut, cutTo := before }
        let g3 : Frame := { f with goal := .const cFail }
        return .cont { M with choices := M.choices.push cp, goals := g1 :: g2 :: g3 :: rest }
      else if c == cFindall && args.size == 2 then
        -- run a nested machine to completion, collecting instances of the goal
        let host ← Backtrackable.save
        let sub : Machine σ :=
          { goals := [{ f with goal := args[0]!, cutTo := 0 }], store := s, fuel := M.fuel }
        let mut cur := sub
        let mut results : Array (Store × Term) := #[]
        let mut err : Option (Step σ) := none
        let mut fuelLeft := M.fuel
        repeat
          match ← runLoop env cur with
          | .yield sol resume =>
            results := results.push (sol.store, args[0]!)
            fuelLeft := resume.fuel
            cur := resume
          | .exhausted => break
          | .outOfFuel => err := some .outOfFuel; break
          | .error e => err := some (.error e); break
        Backtrackable.restore host
        match err with
        | some e => return .done e
        | none =>
          let (items, (s', _)) := (results.mapM fun (st, g) => copyOut st g d).run (s, {})
          let lst := items.foldr (fun x acc => Term.app (.const cCons) #[x, acc]) (.const cNil)
          match unify s' args[1]! lst d with
          | some s'' => return .cont { M with store := s'', goals := rest, fuel := fuelLeft }
          | none => backtrack env { M with goals := rest }
      else callPred env M f c args rest
    | .uvar .. => return .done (.error (.runtime "uninstantiated goal"))
    | _ => return .done (.error (.runtime "ill-formed goal"))

partial def callPred {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ] (env : Env m) (M : Machine σ) (f : Frame) (c : ConstId) (args : Array Term)
      (rest : List Frame) : m (SR σ) := do
    let d := f.depth
    let s := M.store
    let M := { M with goals := rest }
    match env.builtins[c.idx]? with
    | some b =>
      let dargs := args.map (s.deref · d)
      match ← b.run { syms := env.syms, store := s, depth := d } dargs with
      | .fail => backtrack env M
      | .error msg => return .done (.error (.runtime msg))
      | .alts s' l => tryStream env { M with store := s' } f l
    | none =>
      let key := if h : 0 < args.size then Key.ofTerm (s.deref args[0] d) else .flex
      let key := match key with | .flex => .flex | k => k
      let mut cands : Array Cand := #[]
      for lc in f.locals do
        if localHead s lc.term lc.depth == some c then cands := cands.push (.local lc)
      match env.db.preds.find? c with
      | some db =>
        for i in db.candidates key do
          cands := cands.push (.static db.clauses[i]!)
      | none => pure ()
      if cands.isEmpty then
        -- unknown predicate without clauses simply fails
        backtrack env M
      else
        let call : Frame := { f with goal := (if args.isEmpty then .const c else .app (.const c) args),
                                     cutTo := M.choices.size }
        tryClauses env M call cands 0

/-- Run steps until the machine yields, is exhausted, runs out of fuel or fails. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Abstract machine]]
partial def runLoop {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ]
    (env : Env m) (M : Machine σ) : m (Step σ) := do
  match ← stepM env M with
  | .cont M' => runLoop env M'
  | .done r => return r

end

end Elpi
