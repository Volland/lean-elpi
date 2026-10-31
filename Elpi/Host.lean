import Elpi.Runtime.Api
import Elpi.Host.Types
import Elpi.Host.Ast

/-!
# Host API

The stable surface for programs that embed LeanElpi as a library: look up a predicate's
signature, compile named source units, build goals from terms, run them in resumable fuel
slices that return structured terms, add ground facts as terms, and read a program's clauses
as a public AST. A host imports only `Elpi.Host`; the engine modules behind it may change.
-/

-- @lat: [[components#Host API]]

namespace Elpi.Host

/-! ### Signatures -/

/-- An internal type as a `TyTerm`; quantified variables take their declared names. -/
partial def TyTerm.ofTy (names : Array String) : Ty → TyTerm
  | .con n [] => .const n
  | .con n as => .app n (as.map (ofTy names))
  | .arrow a b => .arrow (ofTy names a) (ofTy names b)
  | .gen i => .var (names[i]?.getD s!"'{i}")
  | .mv i => .var s!"?{i}"

/-- The argument types of a predicate type `t1 -> … -> tn -> prop`, or `none` if `ty` does not
end in `prop`. -/
partial def predArgTys (ty : Ty) : Option (List Ty) :=
  match ty with
  | .con "prop" [] => some []
  | .arrow a b => (predArgTys b).map (a :: ·)
  | _ => none

/-- The declared signature of `name`, or `none` when no `pred` or `type … -> prop` declares it.
Arguments of a `type` declaration have mode `o`, as the loader defaults them. -/
-- @tg: implements:: [[openspec:elpi-host-api#Predicate signature lookup]]
def predSig? (p : CompiledProgram) (name : String) : Option PredSig := do
  let sc ← p.sig.consts[name]?
  let tys ← predArgTys sc.ty
  let modes := p.sig.modes.getD name #[]
  let args := tys.toArray.mapIdx fun i t =>
    { mode := modes[i]?.getD .o, ty := TyTerm.ofTy sc.varNames t : Arg }
  return { name, args }

/-! ### Loading -/

private def libraryFind (name : String) (_from : String) : Id (Option (String × String)) :=
  (Std.embedded.find? (·.1 == name)).map fun (n, t) => (n, t)

/-- Parse the units in order, resolving `accumulate` against the embedded libraries. -/
def parseUnits (units : List (String × String)) : Except Error (List Decl) := do
  let mut out : List Decl := []
  for (name, src) in units do
    match Id.run (Elpi.loadUnits libraryFind name src) with
    | .ok ds => out := out ++ ds
    | .error e => throw (.located [Diagnostic.ofPos e.pos e.msg])
  return out

/-- Compile an ordered list of named source units, such as a generated signature followed by a
module, as one program. Parse and type errors are located in the unit they come from. -/
-- @tg: implements:: [[openspec:elpi-host-api#Multi-unit load keeps positions]]
def loadUnits (units : List (String × String)) : Except Error CompiledProgram := do
  let base ← baseProgram |>.mapError .engine
  let ds ← parseUnits units
  match base.addDeclsAt ds with
  | .ok p => return p
  | .error (.type es) => throw (.located (es.map fun e => Diagnostic.ofPos e.pos e.msg))
  | .error (.other e) => throw (.engine e)

/-! ### Clause AST -/

/-- The public clause AST of the units. They are compiled first, so the view is of a program
that parses and type-checks; clauses of accumulated libraries are left out. -/
-- @tg: implements:: [[openspec:elpi-host-api#Public clause AST]]
def ast (units : List (String × String)) : Except Error Ast.Program := do
  let p ← loadUnits units
  let defined := p.definedNames
  let builtins : Std.HashSet String :=
    ((Builtins.core Id).map (·.sig.name) ++ p.extra.map (·.sig.name)).foldl (init := {})
      fun s n => if defined.contains n then s else s.insert n
  let unitNames := units.map (·.1)
  let mut prog : Ast.Program := {}
  for (name, src) in units do
    match Parser.parseProgram name src with
    | .ok raw => prog := { prog with accumulates := prog.accumulates ++ (Ast.accumulatesOf raw).toArray }
    | .error e => throw (.located [Diagnostic.ofPos e.pos e.msg])
  for d in ← parseUnits units do
    match d with
    | .kind names ty pos =>
      if unitNames.contains pos.file then
        prog := { prog with kinds := prog.kinds ++ (names.map (·, Typecheck.kindArity ty)).toArray }
    | .type names _ pos =>
      if unitNames.contains pos.file then
        for n in names do
          if let some sc := p.sig.consts[n]? then
            prog := { prog with types := prog.types.push (n, TyTerm.ofTy sc.varNames sc.ty) }
    | .pred name _ pos _ =>
      if unitNames.contains pos.file then
        if let some ps := predSig? p name then prog := { prog with preds := prog.preds.push ps }
    | .clause attrs t pos =>
      if unitNames.contains pos.file then
        if let some c := Ast.clauseOf builtins attrs (elimSpilling t) pos then
          prog := { prog with clauses := prog.clauses.push c }
    | _ => pure ()
  return prog

/-! ### Goals built from terms -/

/-- A query ready to run: its environment, the symbols it was built with, its output variables
and the machine, which `runSlice` consumes and hands back. -/
structure Query where
  env : Env Id
  syms : Symbols
  names : Array (String × UVarId)
  machine : Machine Unit

/-- A goal argument as surface syntax that never passes through the parser. -/
partial def ResultTerm.toSTm (pos : Pos) : ResultTerm → Except String STm
  | .const n => .ok (.const n pos)
  | .app h args => do
    if args.isEmpty then return .const h pos
    return .app (.const h pos) (← args.toList.mapM (toSTm pos)) pos
  | .int i => .ok (.int i pos)
  | .float b => .ok (.float (Float.ofBits b) pos)
  | .str s => .ok (.str s pos)
  | .list xs => do
    let items ← xs.toList.mapM (toSTm pos)
    return items.foldr (fun x acc => .app (.const "::" pos) [x, acc] pos) (.const "[]" pos)
  | .unbound => .error "an unbound variable is not an input value (use an output argument)"
  | .lam => .error "a λ-abstraction cannot be passed as a value"
  | .opaque t _ => .error s!"opaque host data ({t}) cannot be passed as a value"

/-- Build the goal `pred a1 … an` from terms. Values are handed to the engine as terms, never
printed and parsed; outputs become fresh variables. The goal is type-checked against the
predicate's signature, and a mismatch names the argument. -/
-- @tg: implements:: [[openspec:elpi-host-api#Goals built from terms]]
def buildGoal (p : CompiledProgram) (pred : String) (args : Array GoalArg)
    (fuel : Nat := defaultFuel) : Except Error Query := do
  let some sig := predSig? p pred | throw (.unknownPred pred)
  if sig.args.size != args.size then
    throw (.argument pred 0 s!"{pred} takes {sig.args.size} arguments, {args.size} given")
  -- each argument carries its (1-based) position as its column, so a type error names it
  let mut stms : Array STm := #[]
  for h : i in [0:args.size] do
    let pos : Pos := { file := "<goal>", line := 1, col := i + 1 }
    match args[i] with
    | .value v =>
      match v.toSTm pos with
      | .ok t => stms := stms.push t
      | .error m => throw (.argument pred (i + 1) m)
    | .out n =>
      if n.isEmpty || n.startsWith "_" then
        throw (.argument pred (i + 1) s!"output variable name '{n}' must not be empty or start with '_'")
      stms := stms.push (.var n pos)
  let p0 : Pos := { file := "<goal>", line := 1, col := 0 }
  let goal := if stms.isEmpty then STm.const pred p0 else .app (.const pred p0) stms.toList p0
  match Typecheck.checkProgram p.sig [] (some goal) p.definedNames p.typed with
  | .error (e :: _) =>
    throw (.argument pred (if e.pos.file == "<goal>" then e.pos.col else 0) e.msg)
  | .error [] => throw (.argument pred 0 "ill-typed goal")
  | .ok _ => pure ()
  let prep ← p.prepareTm goal fuel |>.mapError .engine
  return { env := p.env Id prep.syms, syms := prep.syms, names := prep.names, machine := prep.machine }

/-! ### Structured solutions and fuel slices -/

/-- Collect the items of a proper list `x :: xs` (after the first item); `none` if its tail is
not `[]`. -/
partial def listItems (t : Term) (acc : Array Term) : Option (Array Term) :=
  match t with
  | .const c => if c == cNil then some acc else none
  | .app (.const c) #[x, xs] => if c == cCons then listItems xs (acc.push x) else none
  | _ => none

/-- A fully dereferenced term as a `ResultTerm`. -/
-- @tg: implements:: [[openspec:elpi-host-api#Structured solution terms]]
partial def ResultTerm.ofTerm (syms : Symbols) : Term → ResultTerm
  | .const c => if c == cNil then .list #[] else .const (syms.name c)
  | .app (.const c) args =>
    if c == cCons && args.size == 2 then
      match listItems args[1]! #[args[0]!] with
      | some xs => .list (xs.map (ofTerm syms))
      | none => .app "::" (args.map (ofTerm syms))
    else .app (syms.name c) (args.map (ofTerm syms))
  | .app _ _ | .bound _ => .opaque "bound" ""
  | .lit (.int i) => .int i
  | .lit (.float f) => .ofFloat f
  | .lit (.str s) => .str s
  | .uvar .. | .cvar .. => .unbound
  | .lam _ => .lam
  | .builtinData d => .opaque d.typeName d.data

/-- The outcome of one fuel slice. -/
inductive Slice where
  /-- A solution: the output variables in order, the suspended constraints, and the query that
  continues the search after it. -/
  | solution (bindings : Array (String × ResultTerm)) (constraints : List String) (resume : Query)
  | exhausted
  /-- The slice's fuel ran out; `resume` continues the same search. -/
  | paused (resume : Query)
  | error (e : ElpiError)

/-- Hand the slice's leftover fuel back to the budget. -/
@[inline] private def unslice (M : Machine Unit) : Machine Unit :=
  { M with fuel := M.totalFuel, reserve := 0 }

/-- Run at most `n` resolution steps of the query, out of its remaining budget. Slices of any
size give the same solutions in the same order as one run with the whole budget; running out
of the budget itself is `error outOfFuel`. A nested `findall` finishes inside the slice that
starts it, so that slice may run longer than `n`.

Pass the query on without keeping another reference to it, so the store stays uniquely owned
and is updated in place. -/
-- @tg: implements:: [[openspec:elpi-host-api#Resumable fuel slices]]
def runSlice (q : Query) (n : Nat) : Slice :=
  let ⟨env, syms, names, M⟩ := q
  let total := M.totalFuel
  let f := min n total
  match Id.run (runLoop env { M with fuel := f, reserve := total - f }) with
  | .yield sol M' =>
    let bindings := names.map fun (nm, u) => (nm, ResultTerm.ofTerm syms (sol.store.zonk (.uvar u #[]) 0))
    let cs := if sol.constraints.isEmpty then [] else (mkSolution syms names sol).constraintLines
    .solution bindings cs ⟨env, syms, names, unslice M'⟩
  | .paused M' => .paused ⟨env, syms, names, unslice M'⟩
  | .exhausted .. => .exhausted
  | .outOfFuel => .error .outOfFuel
  | .error e => .error e

/-- Every solution of a query, running it in slices of `n` steps; stops at the first error. -/
partial def solveSliced (q : Query) (n : Nat) (limit : Nat := 1000000) :
    Except ElpiError (Array (Array (String × ResultTerm))) :=
  go q #[]
where
  go (q : Query) (acc : Array (Array (String × ResultTerm))) :
      Except ElpiError (Array (Array (String × ResultTerm))) :=
    if acc.size ≥ limit then .ok acc else
    match runSlice q n with
    | .solution bs _ q' => go q' (acc.push bs)
    | .paused q' => go q' acc
    | .exhausted => .ok acc
    | .error e => .error e

/-! ### Bulk facts -/

/-- Substitution of the checker's type variables (`mv i`). -/
structure TySub where
  vars : Array (Option Ty) := #[]

def TySub.fresh (s : TySub) : Ty × TySub := (.mv s.vars.size, { vars := s.vars.push none })

def TySub.bind (s : TySub) (i : Nat) (t : Ty) : TySub := { vars := s.vars.set! i (some t) }

partial def TySub.resolve (s : TySub) : Ty → Ty
  | .mv i => match s.vars[i]? with | some (some t) => s.resolve t | _ => .mv i
  | t => t

partial def TySub.unify (s : TySub) (a b : Ty) : Option TySub :=
  match s.resolve a, s.resolve b with
  | .mv i, .mv j => if i == j then some s else some (s.bind i (.mv j))
  | .mv i, t | t, .mv i => some (s.bind i t)
  | .con n as, .con m bs =>
    if n != m || as.length != bs.length then none
    else (as.zip bs).foldlM (fun s (a, b) => s.unify a b) s
  | .arrow a b, .arrow c d => do s.unify a c >>= (·.unify b d)
  | _, _ => none

/-- A scheme with its quantified variables replaced by fresh checker variables. -/
partial def TySub.instantiate (s : TySub) (sc : Scheme) : Ty × TySub :=
  let base := s.vars.size
  let rec go : Ty → Ty
    | .gen i => .mv (base + i)
    | .con n as => .con n (as.map go)
    | .arrow a b => .arrow (go a) (go b)
    | t => t
  (go sc.ty, { vars := s.vars ++ Array.replicate sc.nvars none })

/-- Check a ground value against the expected type, without the parser. -/
partial def checkValue (sig : Signature) (s : TySub) (v : ResultTerm) (expected : Ty) :
    Except String TySub :=
  let lit (n : String) : Except String TySub :=
    match s.unify expected (.con n []) with
    | some s => .ok s
    | none => .error s!"{v} is a {n}, expected {s.resolve expected}"
  match v with
  | .int _ => lit "int"
  | .float _ => lit "float"
  | .str _ => lit "string"
  | .const n => applied n #[]
  | .app h args => applied h args
  | .list xs =>
    let (el, s) := s.fresh
    match s.unify expected (.con "list" [el]) with
    | none => .error s!"{v} is a list, expected {s.resolve expected}"
    | some s => xs.foldlM (fun s x => checkValue sig s x el) s
  | .unbound | .lam | .opaque .. => .error s!"{v} is not a ground value"
where
  /-- `h args` against `expected`, trying each declared type of an overloaded `h`. -/
  applied (h : String) (args : Array ResultTerm) : Except String TySub := do
    let schemes := (sig.consts[h]?).toList ++ (sig.overloads.getD h #[]).toList
    if schemes.isEmpty then throw s!"unknown constant '{h}'"
    let mut lastErr := ""
    for sc in schemes do
      match tryScheme h sc args with
      | .ok s => return s
      | .error e => lastErr := e
    throw lastErr
  tryScheme (h : String) (sc : Scheme) (args : Array ResultTerm) : Except String TySub := do
    let (ty0, s0) := s.instantiate sc
    let mut s := s0
    let mut ty := ty0
    for a in args do
      match s.resolve ty with
      | .arrow d r =>
        s ← checkValue sig s a d
        ty := r
      | _ => throw s!"'{h}' is applied to too many arguments"
    match s.unify ty expected with
    | some s' => return s'
    | none => throw s!"'{h}' has type {s.resolve ty}, expected {s.resolve expected}"

/-- A ground value as an engine term, interning its constants. -/
partial def ResultTerm.toTerm (syms : Symbols) : ResultTerm → Term × Symbols
  | .const n => let (c, syms) := syms.intern n; (.const c, syms)
  | .app h args =>
    let (c, syms) := syms.intern h
    let (as, syms) := args.foldl (init := (#[], syms)) fun (as, sy) a =>
      let (t, sy) := toTerm sy a
      (as.push t, sy)
    (Term.mkApp (.const c) as, syms)
  | .int i => (.lit (.int i), syms)
  | .float b => (.lit (.float (Float.ofBits b)), syms)
  | .str s => (.lit (.str s), syms)
  | .list xs =>
    let (ts, syms) := xs.foldl (init := (#[], syms)) fun (ts, sy) x =>
      let (t, sy) := toTerm sy x
      (ts.push t, sy)
    (ts.foldr (fun x acc => .app (.const cCons) #[x, acc]) (.const cNil), syms)
  | .unbound | .lam | .opaque .. => (.const cFail, syms)

/-- Check one row against the predicate's declared type. -/
def checkRow (sig : Signature) (sc : Scheme) (pred : String) (row : Nat)
    (vals : Array ResultTerm) : Except Error Unit := do
  let some tys := predArgTys sc.ty | throw (.unknownPred pred)
  if tys.length != vals.size then
    throw (.fact pred row 0 s!"{pred} takes {tys.length} arguments, {vals.size} given")
  -- a fresh instance of the predicate's type per row
  let (ty, s0) := ({} : TySub).instantiate sc
  let argTys := ((predArgTys ty).getD []).toArray
  let mut s := s0
  for h : i in [0:vals.size] do
    match checkValue sig s vals[i] (argTys[i]?.getD (.con "prop" [])) with
    | .ok s' => s := s'
    | .error m => throw (Error.fact pred row (i + 1) m)

/-- The fact `c v1 … vn`, interning its constants. -/
def mkFact (c : ConstId) (vals : Array ResultTerm) (syms : Symbols) : ClauseItem × Symbols :=
  let (args, syms) := vals.foldl (init := (#[], syms)) fun (as, sy) v =>
    let (t, sy) := v.toTerm sy
    (as.push t, sy)
  ({ pred := c, clause := { head := Term.mkApp (.const c) args, body := .const cTrue, nvars := 0 } }, syms)

/-- Check one row and turn it into a fact of `c`. -/
def lowerRow (sig : Signature) (sc : Scheme) (pred : String) (c : ConstId) (row : Nat)
    (vals : Array ResultTerm) (syms : Symbols) : Except Error (ClauseItem × Symbols) := do
  checkRow sig sc pred row vals
  return mkFact c vals syms

/-- Check and lower every row; one bad row fails the whole batch. -/
def lowerRows (sig : Signature) (sc : Scheme) (pred : String) (c : ConstId) :
    Nat → List (Array ResultTerm) → Symbols → Except Error (List ClauseItem × Symbols)
  | _, [], syms => .ok ([], syms)
  | i, r :: rs, syms => do
    let (it, syms) ← lowerRow sig sc pred c i r syms
    let (its, syms) ← lowerRows sig sc pred c (i + 1) rs syms
    return (it :: its, syms)

theorem lowerRows_length {sig : Signature} {sc : Scheme} {pred : String} {c : ConstId} :
    ∀ (i : Nat) (rows : List (Array ResultTerm)) (syms : Symbols) (its : List ClauseItem)
      (syms' : Symbols), lowerRows sig sc pred c i rows syms = .ok (its, syms') →
      its.length = rows.length
  | _, [], _, its, _, h => by
    simp only [lowerRows, Except.ok.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | i, r :: rs, syms, its, syms', h => by
    simp only [lowerRows, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i p _
      split at h
      · simp at h
      · rename_i q hq
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, lowerRows_length (i + 1) rs p.2 q.1 q.2 hq, List.length_cons]

/-- The predicate a batch adds to: its constant and its declared type. -/
def factTarget (p : CompiledProgram) (pred : String) :
    Except Error (ConstId × Scheme × Symbols) := do
  let some sc := p.sig.consts[pred]? | throw (.unknownPred pred)
  if (predArgTys sc.ty).isNone then throw (.unknownPred pred)
  let (c, syms) := p.syms.intern pred
  return (c, sc, syms)

/-- Append lowered facts to their predicate; its index is rebuilt once, in time linear in the
predicate's clauses. -/
def appendFacts (p : CompiledProgram) (c : ConstId) (its : List ClauseItem) (syms : Symbols) :
    CompiledProgram :=
  let old := p.db.preds.findD c {}
  let spec := if old.clauses.isEmpty then p.indexSpecs.getD c.idx #[] else old.spec
  let pdb := PredDB.ofArray (old.clauses ++ its.toArray.map (·.clause)) spec
  { p with syms, items := p.items ++ its.toArray, db := { preds := p.db.preds.insert c pdb } }

/-- Add ground facts of `pred` as terms, without printing or parsing them. Every row is checked
against the predicate's signature; one ill-typed row rejects the whole batch. The original
program stays valid. First-argument indexing applies to the new facts as to parsed clauses. -/
-- @tg: implements:: [[openspec:elpi-host-api#Bulk fact loading]]
def addFacts (p : CompiledProgram) (pred : String) (rows : Array (Array ResultTerm)) :
    Except Error CompiledProgram := do
  let (c, sc, syms) ← factTarget p pred
  let (its, syms) ← lowerRows p.sig sc pred c 1 rows.toList syms
  return appendFacts p c its syms

/-- A batch is all or nothing: on success the program's clause list is the old one followed by
exactly one fact per row, in order, each a fact of the batch's predicate; on failure there is no
program, and the input program is a value that nothing changed. -/
-- @tg: verifies:: [[openspec:elpi-host-api#Bulk fact loading#Ill-typed fact is rejected]]
theorem addFacts_atomic {p p' : CompiledProgram} {pred : String} {rows : Array (Array ResultTerm)}
    (h : addFacts p pred rows = .ok p') :
    ∃ (c : ConstId) (its : List ClauseItem), its.length = rows.size ∧
      p'.items = p.items ++ its.toArray ∧ ∀ it ∈ its, it.pred = c := by
  simp only [addFacts, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i t ht
    split at h
    · simp at h
    · rename_i u hu
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨t.1, u.1, ?_, ?_, ?_⟩
      · rw [lowerRows_length 1 rows.toList t.2.2 u.1 u.2 hu, Array.length_toList]
      · rw [← h]; rfl
      · intro it hit
        exact lowerRows_pred _ _ _ _ _ hu it hit
where
  lowerRows_pred {sig : Signature} {sc : Scheme} {pred : String} {c : ConstId} :
      ∀ (i : Nat) (rows : List (Array ResultTerm)) (syms : Symbols) (its : List ClauseItem)
        (syms' : Symbols), lowerRows sig sc pred c i rows syms = .ok (its, syms') →
        ∀ it ∈ its, it.pred = c := by
    intro i rows
    induction rows generalizing i with
    | nil =>
      intro syms its syms' h it hit
      simp only [lowerRows, Except.ok.injEq, Prod.mk.injEq] at h
      simp [← h.1] at hit
    | cons r rs ih =>
      intro syms its syms' h it hit
      simp only [lowerRows, bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i p hp
        split at h
        · simp at h
        · rename_i q hq
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hit
          cases hit with
          | head => exact lowerRow_pred hp
          | tail _ hm => exact ih (i + 1) p.2 q.1 q.2 hq it hm
  lowerRow_pred {sig : Signature} {sc : Scheme} {pred : String} {c : ConstId} {i : Nat}
      {r : Array ResultTerm} {syms : Symbols} {x : ClauseItem × Symbols}
      (h : lowerRow sig sc pred c i r syms = .ok x) : x.1.pred = c := by
    simp only [lowerRow, bind, Except.bind] at h
    split at h
    · simp at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]; rfl

end Elpi.Host
