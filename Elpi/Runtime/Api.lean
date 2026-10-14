import Std.Data.HashMap
import Elpi.Core.Machine
import Elpi.Std.Std

/-!
# Runtime API

Compile or load programs, run pure, IO or typed queries that return lazy solution
streams, extend programs persistently and attach Lean functions as builtins.
-/

-- @lat: [[components#Runtime API]]

namespace Elpi

/-! ### Lowering surface syntax to terms -/

structure LS where
  syms : Symbols
  vars : Array String := #[]

abbrev LM := StateM LS

def internC (n : String) : LM ConstId := do
  let s ← get
  let (c, syms) := s.syms.intern n
  set { s with syms }
  return c

def freshVar (n : String) : LM Nat := do
  let s ← get
  set { s with vars := s.vars.push n }
  return s.vars.size

def varIdx (n : String) : LM Nat := do
  let s ← get
  match s.vars.findIdx? (· == n) with
  | some i => return i
  | none => freshVar n

partial def lowerTm (binders : Array String) : STm → LM Term
  | .const n _ => do
    match binders.toList.reverse.findIdx? (· == n) with
    | some i => return .bound (binders.size - 1 - i)
    | none => return .const (← internC n)
  | .var n _ => do
    match binders.toList.reverse.findIdx? (· == n) with
    | some i => return .bound (binders.size - 1 - i)
    | none =>
      if n == "_" then
        let i ← freshVar "_"
        return .cvar i #[]
      else return .cvar (← varIdx n) #[]
  | .int i _ => return .lit (.int i)
  | .float f _ => return .lit (.float f)
  | .str s _ => return .lit (.str s)
  | .lam x b _ => do return .lam (← lowerTm (binders.push x) b)
  | .spill _ p => panic! s!"{p.toString}: unexpected spill"
  | .quote _ p => panic! s!"{p.toString}: unelaborated quotation"
  | .term t holes nvars _ => do
    let hs ← holes.toArray.mapM (lowerTm binders)
    let mut vars := hs
    for _ in [hs.size:nvars] do
      let i ← freshVar "_"
      vars := vars.push (.cvar i #[])
    return Term.renameCVars vars binders.size t
  | .app f args _ => do
    let f' ← lowerTm binders f
    let args' ← args.toArray.mapM (lowerTm binders)
    match f' with
    | .lam _ => return Term.applyAt f' args' binders.size
    | _ => return Term.mkApp f' args'

/-- Lower a clause term to a `ClauseItem` (the predicate, head, body and variables). -/
def lowerClause (attrs : Attrs) (t : STm) (pos : Pos) : LM (Option ClauseItem) := do
  modify fun s => { s with vars := #[] }
  let (h, b) := match t with
    | .app (.const ":-" _) [h, b] _ => (h, some b)
    | t => (t, none)
  let hd ← lowerTm #[] h
  let bd ← match b with
    | some b => lowerTm #[] b
    | none => pure (.const cTrue)
  let pred? : Option ConstId := match hd with
    | .const c => some c
    | .app (.const c) _ => some c
    | _ => none
  let nv := (← get).vars.size
  match pred? with
  | none => return none
  | some c =>
    return some
      { pred := c
        clause := { head := hd, body := bd, nvars := nv, name? := attrs.name, pos }
        before? := attrs.before, after? := attrs.after }

/-- Lower a CHR rule: all its terms share the rule's variables. -/
def lowerRule (r : CHRRuleAst) : LM CHRRule := do
  modify fun s => { s with vars := #[] }
  let kept ← r.kept.toArray.mapM (lowerTm #[])
  let removed ← r.removed.toArray.mapM (lowerTm #[])
  let guard ← r.guard.mapM (lowerTm #[])
  let body ← r.body.mapM (lowerTm #[])
  return { kept, removed, guard, body, nvars := (← get).vars.size }

def lowerBlock (preds : List String) (rules : List CHRRuleAst) : LM ConstraintBlock := do
  let ps ← preds.toArray.mapM internC
  let rs ← rules.toArray.mapM lowerRule
  return { preds := ps, rules := rs }

/-! ### Programs -/

structure CompiledProgram where
  syms : Symbols := Symbols.initial
  sig : Signature := {}
  items : Array ClauseItem := #[]
  db : Database := {}
  modes : Std.HashMap Nat (Array Mode) := {}
  /-- Builtins attached at runtime with `withBuiltin`. -/
  extra : List (Builtin Id) := []
  /-- CHR blocks, in source order. -/
  blocks : Array ConstraintBlock := #[]
  /-- Native constraint handlers (tier T3) and unification hooks (tier T4). -/
  handlers : List (String × ConstraintHandler) := []
  hooks : Array UnifHook := #[]
  deriving Inhabited

private def joinErrs (es : List TypeError) : String :=
  "\n".intercalate (es.map TypeError.toString)

/-- Process declarations on top of an existing program state: update the signature,
typecheck every clause, lower clauses and rebuild the clause database. -/
def CompiledProgram.definedNames (p : CompiledProgram) : Std.HashSet String :=
  p.items.foldl (fun s it => s.insert (p.syms.name it.pred)) {}

def CompiledProgram.addDecls (p : CompiledProgram) (decls : List Decl) :
    Except ElpiError CompiledProgram := do
  let mut sig := p.sig
  for d in decls do
    match checkSignature' sig d with
    | .ok s => sig := s
    | .error e => throw (.type e.toString)
  let mut clauses : Array (Attrs × STm × Pos) := #[]
  for d in decls do
    if let .clause a t pos := d then
      if let some q := findQuote t then
        throw (.load s!"{q.toString}: Lean quotations need a Lean environment (use elpi_accumulate or #elpi)")
      if let some (q, what) := unsupportedFeature t then
        throw (.load s!"{q.toString}: '{what}' is unsupported in this milestone")
      clauses := clauses.push (a, elimSpilling t, pos)
  -- the terms of a CHR rule are checked like one clause body (they share variables)
  let mut ruleTerms : List STm := []
  for d in decls do
    if let .constraint _ rs _ := d then
      for r in rs do
        let ts := r.kept ++ r.removed ++ r.guard.toList ++ r.body.toList
        match ts with
        | [] => pure ()
        | t :: more =>
          ruleTerms := ruleTerms ++ [more.foldl (fun acc x => STm.app (.const "," r.pos) [acc, x] r.pos) t]
  let known := ruleTerms.foldl (init := p.definedNames) fun s t =>
    (Typecheck.clauseHead t).elim s s.insert
  match Typecheck.checkProgram sig (clauses.toList.map (·.2.1) ++ ruleTerms) none known with
  | .error es => throw (.type (joinErrs es))
  | .ok () => pure ()
  let (items, ls) := (clauses.mapM fun (a, t, pos) => lowerClause a t pos).run { syms := p.syms }
  let items := p.items ++ items.filterMap id
  let lists ← graft items
  let mut ls := ls
  let mut blocks := p.blocks
  for d in decls do
    if let .constraint ps rs _ := d then
      let (b, ls') := (lowerBlock ps rs).run ls
      ls := ls'
      blocks := blocks.push b
  -- a native handler owns its predicates: CHR blocks over them are rejected
  for b in blocks do
    for (hn, h) in p.handlers do
      for k in h.keys do
        if let some c := ls.syms.find? k then
          if b.preds.contains c then
            throw (.load s!"constraint block over '{k}', which the native handler '{hn}' owns")
  let modes := sig.modes.fold (init := p.modes) fun m n ms =>
    match ls.syms.find? n with
    | some c => m.insert c.idx ms
    | none => m
  return { p with syms := ls.syms, sig, items, db := Database.ofLists lists, modes, blocks }
where
  checkSignature' (sig : Signature) (d : Decl) : Except TypeError Signature :=
    Typecheck.checkSignature sig d

/-- The prelude and standard library, parsed once. -/
def stdDecls : Except ElpiError (List Decl) :=
  match Parser.parseProgram "builtin.elpi" Std.builtinSource,
        Parser.parseProgram "std.elpi" Std.source with
  | .ok a, .ok b => .ok (a ++ b)
  | .error e, _ | _, .error e => .error (.parse e.toString)

/-- The program with only the prelude and the standard library loaded. -/
def baseProgram : Except ElpiError CompiledProgram := do
  let ds ← stdDecls
  ({} : CompiledProgram).addDecls ds

/-- Counts how often the parser ran in this process (tests use it to show that compiled
programs are not parsed at runtime). -/
initialize parserCalls : IO.Ref Nat ← IO.mkRef 0

@[noinline] unsafe def bumpParserCalls (n : Nat) : Nat :=
  unsafeBaseIO (do parserCalls.modify (· + 1); pure n)

@[implemented_by bumpParserCalls]
opaque noteParse (n : Nat) : Nat

namespace Program

/-- Parse, resolve accumulations (against the embedded libraries), typecheck and
compile a program text. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Runtime program loading]]
def loadWith (sigs : List String) (src : String) (file : String := "<string>") :
    Except ElpiError CompiledProgram := do
  if noteParse 0 > 1000000000000 then throw (.load "parser counter overflow")
  let base ← baseProgram
  let mut pre : List Decl := []
  for sg in sigs do
    match Parser.parseProgram "<signature>" sg with
    | .ok ds => pre := pre ++ ds
    | .error e => throw (.parse e.toString)
  let find (name : String) (_from : String) : Id (Option (String × String)) :=
    (Std.embedded.find? (·.1 == name)).map fun (n, t) => (n, t)
  match Id.run (loadUnits find file src) with
  | .error e => throw (.parse e.toString)
  | .ok ds => base.addDecls (pre ++ ds)

def load (src : String) (file : String := "<string>") : Except ElpiError CompiledProgram :=
  loadWith [] src file

end Program

/-! ### Solutions -/

/-- One solution of a query: bindings of the query's named variables (fully dereferenced,
in order of first occurrence) and the residual suspended problems. -/
structure Solution where
  bindings : List (String × Term)
  /-- Constraints still suspended when the answer was found (goals fully dereferenced). -/
  constraints : List Constraint := []
  syms : Symbols
  store : Store

/-- Render a term with the program's symbol names. -/
def Solution.show (s : Solution) (t : Term) : String :=
  (Print.pp t 0 0 true).run' { syms := s.syms, store := s.store }

def Solution.toString (s : Solution) : String :=
  let items := s.bindings.map fun (n, t) => s!"{n} = {s.show t}"
  ", ".intercalate items

instance : ToString Solution := ⟨Solution.toString⟩

/-- Residual constraints in the oracle's format, newest first: the goal and the variables
it is suspended on, with the eigenvariables of its scope in front. Variable names are
shared across the whole list. -/
-- @tg: implements:: [[openspec:elpi-constraints#Residual constraints]]
def Solution.constraintLines (s : Solution) : List String :=
  let act : Print.PM (List String) := do
    let mut out : List String := []
    for c in s.constraints.reverse do
      let g ← Print.pp c.goal c.depth 0 false
      let ks ← c.keys.toList.filterMapM fun k => do
        match (← get).store.deref (.uvar k #[]) 0 with
        | .uvar u _ => return some (← Print.varName u)
        | _ => return none
      let scope := if c.depth == 0 then "" else
        "{" ++ ", ".intercalate ((List.range c.depth).map fun i => s!"c{i}") ++ "} : "
      out := out ++ [s!" {scope}{g}  /* suspended on {", ".intercalate ks} */"]
    return out
  (act.run' { syms := s.syms, store := s.store })

def Solution.find? (s : Solution) (n : String) : Option Term := s.bindings.lookup n


/-- Default fuel budget: resolution steps per run. -/
def defaultFuel : Nat := 100000000

structure Prepared where
  machine : Machine Unit
  syms : Symbols
  names : Array (String × UVarId)

def CompiledProgram.env (p : CompiledProgram) (m : Type → Type) [Monad m] [Output m]
    (syms : Symbols := p.syms) : Env m :=
  let core := Builtins.core m
  let lift (b : Builtin Id) : Builtin m := { sig := b.sig, run := fun c a => pure (b.run c a) }
  let all := core ++ p.extra.map lift
  { syms, db := p.db, modes := p.modes
    blocks := p.blocks
    handlers := p.handlers.foldl (init := {}) fun h (n, hd) =>
      hd.keys.foldl (init := h) fun h k =>
        match syms.find? k with
        | some c => h.insert c.idx (n, hd)
        | none => h
    builtins := all.foldl (init := {}) fun h b =>
      match syms.find? b.sig.name with
      | some c => h.insert c.idx b
      | none => h }

/-- Typecheck and lower a parsed query; returns the initial machine. -/
def CompiledProgram.prepareTm (p : CompiledProgram) (t : STm) (fuel : Nat := defaultFuel) :
    Except ElpiError Prepared := do
  if let some q := findQuote t then
    throw (.load s!"{q.toString}: Lean quotations need a Lean environment (use #elpi)")
  let (t', _) := elimGoal t 0
  match Typecheck.checkProgram p.sig [] (some t') p.definedNames with
  | .error es => throw (.type (joinErrs es))
  | .ok () => pure ()
  let (goal, ls) := (lowerTm #[] t').run { syms := p.syms }
  -- query variables become unification variables at level 0
  let mut store : Store :=
    { hooks := p.hooks
      interp := p.hooks.foldl (init := #[]) fun a h =>
        h.interpreted.foldl (init := a) fun a n => match ls.syms.find? n with | some c => a.push c.idx | none => a }
  let mut vars : Array Term := #[]
  let mut names : Array (String × UVarId) := #[]
  for n in ls.vars do
    let (u, s') := store.fresh 0 (some n)
    store := s'
    vars := vars.push (.uvar u #[])
    if n != "_" && !n.startsWith "_" then names := names.push (n, u)
  let g := Machine.rename vars 0 goal
  return { machine := { goals := [{ goal := g, depth := 0, locals := [], cutTo := 0 }]
                        store, fuel }
           syms := ls.syms
           names }

/-- Build the initial machine from a goal constructed directly as a term: `vars` are fresh
query variables (level 0) handed to `mk`. No typechecking: the caller vouches for the term. -/
def CompiledProgram.prepareRaw (p : CompiledProgram) (vars : List String)
    (mk : Array Term → Term) (fuel : Nat := defaultFuel) : Prepared := Id.run do
  let mut store : Store :=
    { hooks := p.hooks
      interp := p.hooks.foldl (init := #[]) fun a h =>
        h.interpreted.foldl (init := a) fun a n => match p.syms.find? n with | some c => a.push c.idx | none => a }
  let mut vs : Array Term := #[]
  let mut names : Array (String × UVarId) := #[]
  for n in vars do
    let (u, s') := store.fresh 0 (some n)
    store := s'
    vs := vs.push (.uvar u #[])
    names := names.push (n, u)
  return { machine := { goals := [{ goal := mk vs, depth := 0, locals := [], cutTo := 0 }], store, fuel }
           syms := p.syms, names }

/-- Parse, typecheck and lower a query; returns the initial machine. -/
def CompiledProgram.prepare (p : CompiledProgram) (q : String) (fuel : Nat := defaultFuel) :
    Except ElpiError Prepared := do
  let t ← match Parser.parseQuery "<query>" q with
    | .ok t => pure t
    | .error e => throw (.parse e.toString)
  p.prepareTm t fuel

def mkSolution (syms : Symbols) (names : Array (String × UVarId)) (sol : RawSolution) :
    Solution :=
  { bindings := names.toList.map fun (n, u) => (n, sol.store.zonk (.uvar u #[]) 0)
    constraints := sol.constraints.map fun c => { c with goal := sol.store.zonk c.goal c.depth }, syms, store := sol.store }

/-- Run a query purely: a lazy stream of solutions. A resource error or engine error is a
terminal `Except.error` element, distinguishable from exhaustion. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Pure lazy queries]]
partial def solve (p : CompiledProgram) (q : String) (fuel : Nat := defaultFuel) :
    LazyList (Except ElpiError Solution) :=
  match p.prepare q fuel with
  | .error e => .cons (.error e) (Thunk.mk fun _ => .nil)
  | .ok prep => go (p.env Id prep.syms) prep.syms prep.names prep.machine
where
  go (env : Env Id) (syms : Symbols) (names : Array (String × UVarId)) (M : Machine Unit) :
      LazyList (Except ElpiError Solution) :=
    match Id.run (runLoop env M) with
    | .yield sol M' =>
      .cons (.ok (mkSolution syms names sol)) (Thunk.mk fun _ => go env syms names M')
    | .exhausted => .nil
    | .outOfFuel => .cons (.error .outOfFuel) (Thunk.mk fun _ => .nil)
    | .error e => .cons (.error e) (Thunk.mk fun _ => .nil)

/-- A stream in `IO`: each call to `next` computes one more solution. -/
structure IOStream (α : Type) where
  next : IO (Option α)

/-- Run a query in `IO`, so `print` writes to standard output as the search reaches it.
Engine errors are raised as `IO` exceptions. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#IO queries]]
def solveIO (p : CompiledProgram) (q : String) (fuel : Nat := defaultFuel) :
    IO (IOStream Solution) := do
  match p.prepare q fuel with
  | .error e => throw (IO.userError (toString e))
  | .ok prep =>
    let env : Env IO := p.env IO prep.syms
    let ref ← IO.mkRef (some prep.machine)
    return { next := do
      match ← ref.get with
      | none => return none
      | some M =>
        match ← runLoop env M with
        | .yield sol M' =>
          ref.set (some M')
          return some (mkSolution prep.syms prep.names sol)
        | .exhausted => ref.set none; return none
        | .outOfFuel => ref.set none; throw (IO.userError (toString ElpiError.outOfFuel))
        | .error e => ref.set none; throw (IO.userError (toString e)) }

/-! ### Typed decoding -/

/-- A decoding failure: what was expected and the term that was found. -/
structure DecodeError where
  expected : String
  got : String
  deriving Inhabited

def DecodeError.toString (e : DecodeError) : String :=
  s!"cannot decode: expected {e.expected} but got {e.got}"

instance : ToString DecodeError := ⟨DecodeError.toString⟩

def showTerm (t : Term) : String :=
  (Print.pp t 0 0 true).run' { syms := Symbols.initial, store := {} }

def DecodeError.mk' (expected : String) (t : Term) : DecodeError :=
  { expected, got := showTerm t }

-- @tg: implements:: [[openspec:lean-reflection#Typed marshalling classes]]
class FromElpi (α : Type) where
  tyName : String
  fromElpi : Term → Except DecodeError α

export FromElpi (fromElpi)

instance : FromElpi Int where
  tyName := "Int"
  fromElpi | .lit (.int i) => .ok i | t => .error (.mk' "int" t)
instance : FromElpi Nat where
  tyName := "Nat"
  fromElpi | .lit (.int i) => if i ≥ 0 then .ok i.toNat else .error (.mk' "int" (.lit (.int i)))
           | t => .error (.mk' "int" t)
instance : FromElpi String where
  tyName := "String"
  fromElpi | .lit (.str s) => .ok s | t => .error (.mk' "string" t)
instance : FromElpi Float where
  tyName := "Float"
  fromElpi | .lit (.float f) => .ok f | t => .error (.mk' "float" t)
instance : FromElpi Bool where
  tyName := "Bool"
  fromElpi | .const c => if c == cTT || c == cTrue then .ok true
                         else if c == cFF || c == cFail then .ok false
                         else .error (.mk' "bool" (.const c))
           | t => .error (.mk' "bool" t)
instance : FromElpi Term where
  tyName := "term"
  fromElpi t := .ok t

partial def decodeList {α : Type} (f : Term → Except DecodeError α) (t0 : Term) :
    Except DecodeError (List α) :=
  let rec go : Term → Except DecodeError (List α)
    | .const c => if c == cNil then .ok [] else .error (.mk' "list" t0)
    | .app (.const c) #[x, xs] =>
      if c == cCons then do
        let a ← f x
        let rest ← go xs
        return a :: rest
      else .error (.mk' "list" t0)
    | _ => .error (.mk' "list" t0)
  go t0

instance {α : Type} [FromElpi α] : FromElpi (List α) where
  tyName := s!"List {FromElpi.tyName α}"
  fromElpi t := decodeList FromElpi.fromElpi t
instance {α : Type} [FromElpi α] : FromElpi (Array α) where
  tyName := s!"List {FromElpi.tyName α}"
  fromElpi t := (decodeList FromElpi.fromElpi t).map List.toArray
instance {α : Type} [FromElpi α] : FromElpi (Option α) where
  tyName := s!"Option {FromElpi.tyName α}"
  fromElpi
    | .const c => if c == cNone then .ok none else .error (.mk' "option" (.const c))
    | .app (.const c) #[x] =>
      if c == cSome then (FromElpi.fromElpi x).map some else .error (.mk' "option" (.app (.const c) #[x]))
    | t => .error (.mk' "option" t)
instance {α β : Type} [FromElpi α] [FromElpi β] : FromElpi (α × β) where
  tyName := s!"{FromElpi.tyName α} × {FromElpi.tyName β}"
  fromElpi
    | .app (.const c) #[x, y] =>
      if c == cPair then do
        let a ← FromElpi.fromElpi x
        let b ← FromElpi.fromElpi y
        return (a, b)
      else .error (.mk' "pair" (.app (.const c) #[x, y]))
    | t => .error (.mk' "pair" t)

/-- Decoding the bindings of a solution: one variable through `FromElpi`, several
variables as a product. -/
class FromBindings (α : Type) where
  tyName : String
  decode : List (String × Term) → Except ElpiError α

instance (priority := low) {α : Type} [FromElpi α] : FromBindings α where
  tyName := FromElpi.tyName α
  decode
    | [(n, t)] =>
      match FromElpi.fromElpi t with
      | .ok a => .ok a
      | .error _ => .error (.runtime s!"cannot decode variable {n} as {FromElpi.tyName α}")
    | bs => .error (.runtime s!"expected one answer variable, found {bs.length}")

instance {α β : Type} [FromElpi α] [FromBindings β] : FromBindings (α × β) where
  tyName := s!"{FromElpi.tyName α} × {FromBindings.tyName β}"
  decode
    | (n, t) :: rest =>
      match FromElpi.fromElpi t with
      | .ok a => (FromBindings.decode rest).map (a, ·)
      | .error _ => .error (.runtime s!"cannot decode variable {n} as {FromElpi.tyName α}")
    | [] => .error (.runtime "no answer variables")

/-- Run a query and decode the answer variables into a Lean value. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Typed query decoding]]
partial def solveAs {α : Type} [FromBindings α] (p : CompiledProgram) (q : String)
    (fuel : Nat := defaultFuel) : LazyList (Except ElpiError α) :=
  go (solve p q fuel)
where
  go : LazyList (Except ElpiError Solution) → LazyList (Except ElpiError α)
    | .nil => .nil
    | .cons (.error e) tl => .cons (.error e) (Thunk.mk fun _ => go tl.get)
    | .cons (.ok s) tl =>
      .cons (FromBindings.decode s.bindings) (Thunk.mk fun _ => go tl.get)


/-- The binding of a query variable, decoded into a Lean value. -/
def Solution.get? {α : Type} [FromElpi α] (s : Solution) (n : String) : Option α :=
  match s.bindings.lookup n with
  | some t => (FromElpi.fromElpi t).toOption
  | none => none

/-! ### Encoding -/

class ToElpi (α : Type) where
  toElpi : α → Term

export ToElpi (toElpi)

instance : ToElpi Int := ⟨fun i => .lit (.int i)⟩
instance : ToElpi Nat := ⟨fun i => .lit (.int i)⟩
instance : ToElpi String := ⟨fun s => .lit (.str s)⟩
instance : ToElpi Float := ⟨fun f => .lit (.float f)⟩
instance : ToElpi Bool := ⟨fun b => .const (if b then cTT else cFF)⟩
instance : ToElpi Term := ⟨id⟩
instance {α : Type} [ToElpi α] : ToElpi (List α) :=
  ⟨fun l => l.foldr (fun x acc => .app (.const cCons) #[ToElpi.toElpi x, acc]) (.const cNil)⟩
instance {α : Type} [ToElpi α] : ToElpi (Array α) :=
  ⟨fun l => l.toList.foldr (fun x acc => .app (.const cCons) #[ToElpi.toElpi x, acc]) (.const cNil)⟩
instance {α : Type} [ToElpi α] : ToElpi (Option α) :=
  ⟨fun | none => .const cNone | some x => .app (.const cSome) #[ToElpi.toElpi x]⟩
instance {α β : Type} [ToElpi α] [ToElpi β] : ToElpi (α × β) :=
  ⟨fun (a, b) => .app (.const cPair) #[ToElpi.toElpi a, ToElpi.toElpi b]⟩

/-- The ELPI `int` range (63-bit signed). -/
def elpiIntMin : Int := -(2 ^ 62)
def elpiIntMax : Int := 2 ^ 62 - 1

/-- Range-checked encoding of numbers: outside the ELPI `int` range it is an error, not a
wrapped value. -/
def encodeInt (i : Int) : Except String Term :=
  if elpiIntMin ≤ i && i ≤ elpiIntMax then .ok (.lit (.int i))
  else .error s!"integer {i} is outside the range of the ELPI int type"

def encodeNat (n : Nat) : Except String Term := encodeInt n

/-! ### Extending programs -/

/-- Append a clause to its predicate, after typechecking against the signature. The
original program is unchanged; the clause database is shared. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Persistent program extension]]
def CompiledProgram.assert (p : CompiledProgram) (clause : String) :
    Except ElpiError CompiledProgram := do
  if noteParse 0 > 1000000000000 then throw (.load "parser counter overflow")
  let ds ← match Parser.parseProgram "<assert>" clause with
    | .ok ds => pure ds
    | .error e => throw (.parse e.toString)
  let mut sig := p.sig
  let mut clauses : Array (Attrs × STm × Pos) := #[]
  for d in ds do
    match d with
    | .clause a t pos => clauses := clauses.push (a, elimSpilling t, pos)
    | _ => throw (.load "assert expects clauses")
  match Typecheck.checkProgram sig (clauses.toList.map (·.2.1)) none p.definedNames with
  | .error es => throw (.type (joinErrs es))
  | .ok () => pure ()
  let (items, ls) := (clauses.mapM fun (a, t, pos) => lowerClause a t pos).run { syms := p.syms }
  let mut db := p.db
  let mut allItems := p.items
  for it in items.filterMap id do
    db := db.assert it.pred it.clause
    allItems := allItems.push it
  sig := p.sig
  return { p with syms := ls.syms, db, items := allItems }

/-- Attach a Lean function as the predicate `name`, with a typechecked signature. The
function receives the (zonked) arguments and returns, per alternative, the values of the
output-mode arguments. -/
-- @tg: implements:: [[openspec:elpi-runtime-library#Runtime builtins]]
def CompiledProgram.withBuiltin (p : CompiledProgram) (name : String) (sigSrc : String)
    (f : Array Term → LazyList (Array Term)) : Except ElpiError CompiledProgram := do
  let ds ← match Parser.parseProgram "<builtin>" sigSrc with
    | .ok ds => pure ds
    | .error e => throw (.parse e.toString)
  let defined := match p.syms.find? name with
    | some c => p.db.preds.contains c
    | none => false
  if p.sig.consts.contains name || defined then
    throw (.load s!"builtin '{name}' clashes with an existing predicate")
  let mut sig := p.sig
  for d in ds do
    match Typecheck.checkSignature sig d with
    | .ok s => sig := s
    | .error e => throw (.type e.toString)
  let (_, syms) := p.syms.intern name
  let modes := (sig.modes[name]?).getD #[]
  let b : Builtin Id :=
    Builtin.ofOutputs { name, modes, type := .con "any" [] } fun ctx args =>
      f (args.map (ctx.store.zonk · ctx.depth))
  return { p with syms, sig, modes := p.modes.insert (syms.find? name).get!.idx modes,
                  extra := b :: p.extra }

/-- Convenience: a builtin with one input and one output computed by a Lean function that
returns the list of alternatives. -/
def CompiledProgram.withFn1 {α β : Type} [FromElpi α] [ToElpi β] (p : CompiledProgram)
    (name sigSrc : String) (f : α → List β) : Except ElpiError CompiledProgram :=
  p.withBuiltin name sigSrc fun args =>
    match FromElpi.fromElpi args[0]! with
    | .ok a => LazyList.ofList (f a |>.map fun b => #[ToElpi.toElpi b])
    | .error _ => .nil

/-- Run a query in an arbitrary host monad, collecting up to `limit` solutions. The
builtins in `extra` are available in addition to the core ones. -/
def runPrepared {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ] [Output m]
    (p : CompiledProgram) (prepE : Except ElpiError Prepared) (extra : List (Builtin m) := [])
    (limit : Nat := 1000) : m (Except ElpiError (List Solution)) := do
  match prepE with
  | .error e => return .error e
  | .ok prep =>
    let base := p.env m prep.syms
    let env : Env m :=
      { base with builtins := extra.foldl (init := base.builtins) fun h b =>
                    match prep.syms.find? b.sig.name with
                    | some c => h.insert c.idx b
                    | none => h }
    let M : Machine σ := { goals := prep.machine.goals, store := prep.machine.store,
                           fuel := prep.machine.fuel }
    let mut cur := M
    let mut out : Array Solution := #[]
    while out.size < limit do
      match ← runLoop env cur with
      | .yield sol M' => out := out.push (mkSolution prep.syms prep.names sol); cur := M'
      | .exhausted => break
      | .outOfFuel => return .error .outOfFuel
      | .error e => return .error e
    return .ok out.toList

def runIn {m : Type → Type} {σ : Type} [Monad m] [Backtrackable m σ] [Output m]
    (p : CompiledProgram) (q : String) (extra : List (Builtin m) := [])
    (limit : Nat := 1000) (fuel : Nat := defaultFuel) : m (Except ElpiError (List Solution)) :=
  runPrepared p (p.prepare q fuel) extra limit

/-- Quote a command-line argument as an ELPI string literal. -/
def quoteArg (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- Print the residual constraints of an answer on standard error, as the oracle does. -/
def reportConstraints (sol : Solution) : IO Unit := do
  let ls := sol.constraintLines
  unless ls.isEmpty do
    IO.eprintln "Constraints:"
    for l in ls do IO.eprintln l
    IO.eprintln "State:"

/-- Run the first solution of a query; exit status 0 on success, 1 on failure or error. -/
def runOnce (p : CompiledProgram) (q : String) (fuel : Nat := defaultFuel) : IO UInt32 := do
  try
    let st ← solveIO p q fuel
    match ← st.next with
    | some sol => reportConstraints sol; return 0
    | none =>
      IO.eprintln "Failure"
      return 1
  catch e =>
    IO.eprintln s!"{e}"
    return 1

/-- Entry point of compiled executables: run `main [ARGS…]`. -/
def runMain (p : CompiledProgram) (args : List String) : IO UInt32 :=
  runOnce p s!"main [{", ".intercalate (args.map quoteArg)}]"

/-- Register a native constraint handler (tier T3). A name clash is an error. -/
def CompiledProgram.withHandler (p : CompiledProgram) (name : String) (h : ConstraintHandler) :
    Except ElpiError CompiledProgram := do
  if p.handlers.any (·.1 == name) then throw (.load s!"constraint handler '{name}' is already registered")
  let (syms, owned) := h.keys.foldl (init := (p.syms, ([] : List ConstId))) fun (sy, os) k =>
    let (c, sy) := sy.intern k
    (sy, c :: os)
  for b in p.blocks do
    if owned.any b.preds.contains then
      throw (.load s!"constraint block over a predicate owned by the native handler '{name}'")
  return { p with syms, handlers := p.handlers ++ [(name, h)] }

/-- Register a unification hook (tier T4); hooks are consulted in registration order. -/
def CompiledProgram.withHook (p : CompiledProgram) (h : UnifHook) : CompiledProgram :=
  let syms := h.interpreted.foldl (fun sy n => (sy.intern n).2) p.syms
  { p with syms, hooks := p.hooks.push h }

end Elpi
