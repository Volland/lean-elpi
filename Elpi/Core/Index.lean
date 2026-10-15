import Std.Data.HashMap
import Lean.Data.PersistentHashMap
import Elpi.Core.Term
import Elpi.Core.Parser
import Elpi.Core.Typecheck

/-!
# Clause index

The symbol table, compiled clauses, per-predicate clause order with `:name`/`:before`/
`:after` grafting, and first-argument indexing. The clause database is a persistent map
so that asserting a clause shares structure with the original program.
-/

-- @lat: [[components#Clause index]]

namespace Elpi

/-- Interned constants. The reserved control constants have small fixed ids; every other
name gets an id determined by the name itself (a hash, probed on the rare collision), so a
`ConstId` means the same thing in every program and Lean values can be encoded without a
symbol table. -/
structure Symbols where
  byId : Std.HashMap Nat String := {}
  ids : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Id of a non-reserved name: above the reserved range, a function of the name only. -/
def symbolId (n : String) : Nat := 1048576 + (hash n).toNat % (2 ^ 40)

def Symbols.intern (s : Symbols) (n : String) : ConstId × Symbols :=
  match s.ids[n]? with
  | some i => (⟨i⟩, s)
  | none =>
    let rec probe (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => i
      | f + 1 => if s.byId.contains i then probe (i + 1) f else i
    let i := probe (symbolId n) 4096
    (⟨i⟩, { byId := s.byId.insert i n, ids := s.ids.insert n i })

def Symbols.find? (s : Symbols) (n : String) : Option ConstId := (s.ids[n]?).map (⟨·⟩)

def Symbols.name (s : Symbols) (c : ConstId) : String := (s.byId[c.idx]?).getD s!"<const {c.idx}>"

def reservedNames : Array String :=
  #["true", "fail", "!", ",", ";", "=>", "pi", "sigma", "=", "not", ":-", "[]", "::",
    "findall_solutions", "->", "<=", "halt", "print", "some", "none", "pr", "tt", "ff", "?-", "declare_constraint",
    -- the reflection of Lean terms (`lean.elpi`) and the tactic interface
    "const", "app", "fun", "forall", "let", "sort", "lit", "mvar", "fvar", "proj", "mdata",
    "nat", "str", "decl", "goal", "int", "trm"]

def cTrue : ConstId := ⟨0⟩
def cFail : ConstId := ⟨1⟩
def cCut : ConstId := ⟨2⟩
def cConj : ConstId := ⟨3⟩
def cOr : ConstId := ⟨4⟩
def cImpl : ConstId := ⟨5⟩
def cPi : ConstId := ⟨6⟩
def cSigma : ConstId := ⟨7⟩
def cEq : ConstId := ⟨8⟩
def cNot : ConstId := ⟨9⟩
def cNeck : ConstId := ⟨10⟩
def cNil : ConstId := ⟨11⟩
def cCons : ConstId := ⟨12⟩
def cFindall : ConstId := ⟨13⟩
def cArrow : ConstId := ⟨14⟩
def cRImpl : ConstId := ⟨15⟩
def cSome : ConstId := ⟨18⟩
def cNone : ConstId := ⟨19⟩
def cPair : ConstId := ⟨20⟩
def cTT : ConstId := ⟨21⟩
def cFF : ConstId := ⟨22⟩
def cTurn : ConstId := ⟨23⟩
def cDeclare : ConstId := ⟨24⟩
-- constructors of the reflected Lean `term` type, see `Elpi/Lean/Reflect.lean`
def cConstR : ConstId := ⟨25⟩
def cAppR : ConstId := ⟨26⟩
def cFunR : ConstId := ⟨27⟩
def cForallR : ConstId := ⟨28⟩
def cLetR : ConstId := ⟨29⟩
def cSortR : ConstId := ⟨30⟩
def cLitR : ConstId := ⟨31⟩
def cMVarR : ConstId := ⟨32⟩
def cFVarR : ConstId := ⟨33⟩
def cProjR : ConstId := ⟨34⟩
def cMDataR : ConstId := ⟨35⟩
def cNatLitR : ConstId := ⟨36⟩
def cStrLitR : ConstId := ⟨37⟩
def cDeclR : ConstId := ⟨38⟩
def cGoalR : ConstId := ⟨39⟩
def cIntArgR : ConstId := ⟨40⟩
def cTrmArgR : ConstId := ⟨41⟩

def Symbols.initial : Symbols := Id.run do
  let mut s : Symbols := {}
  for i in [0:reservedNames.size] do
    s := { byId := s.byId.insert i reservedNames[i]!, ids := s.ids.insert reservedNames[i]! i }
  return s

/-- The id of a constant by name: the reserved id for control and reflection constants, the
hash id for everything else. -/
def constIdOf (n : String) : ConstId :=
  match Symbols.initial.find? n with
  | some c => c
  | none => ⟨symbolId n⟩

/-- Names interned beyond the reserved ones. -/
def Symbols.userNames (s : Symbols) : List String :=
  s.ids.toList.filterMap fun (n, i) => if i < reservedNames.size then none else some n

/-- A compiled clause; `cvar i` ranges over `i < nvars`. `args` and `goals` are filled by
`Clause.compile` when the clause enters a `PredDB`: the head's arguments, and the body as a
flat sequence of goals (top-level `,` split, `true` dropped). -/
structure Clause where
  head : Term
  body : Term
  nvars : Nat
  name? : Option String := none
  pos : Pos := {}
  args : Array Term := #[]
  goals : Array Term := #[]
  /-- For an `:index` predicate: per indexed argument, `groundHash` of the head's argument (0: it
  has a variable within the indexed depth). Filled when the clause enters a `PredDB`. -/
  ihash : Array UInt64 := #[]
  deriving Inhabited

/-- The goals of a clause body: conjunctions split, `true` dropped, in order. -/
partial def flattenBody (t : Term) (acc : Array Term := #[]) : Array Term :=
  match t with
  | .app (.const c) #[a, b] => if c == cConj then flattenBody b (flattenBody a acc) else acc.push t
  | .const c => if c == cTrue then acc else acc.push t
  | _ => acc.push t

-- @tg: implements:: [[openspec:elpi-core-engine#Compiled clauses and term sharing]]
/-- A hash of `t` to `n` levels (only the head and arity at the deepest level), or `0` when a
variable, λ or bound name occurs within them. Two terms with different non-zero hashes clash
rigidly within `n` levels, so a clause and a call whose hashes differ cannot unify. `deref`
gives the head of a term (a call's arguments may contain assigned variables). -/
partial def groundHash (deref : Term → Term) (t : Term) (n : Nat) : UInt64 :=
  if n == 0 then 1 else
  -- a rigid term never hashes to 0, which is reserved for "has a variable"
  let nz (h : UInt64) : UInt64 := if h == 0 then 1 else h
  match deref t with
  | .const c => nz (mixHash 2 (hash c.idx))
  | .lit l => nz (mixHash 3 (hash l))
  | .app (.const c) as =>
    let h0 := mixHash (mixHash 4 (hash c.idx)) (hash as.size)
    if n == 1 then nz h0 else Id.run do
      let mut h := h0
      for a in as do
        let g := groundHash deref a (n - 1)
        if g == 0 then return 0
        h := mixHash h g
      return nz h
  | _ => 0

/-- The per-argument hashes of a head's arguments under an `:index` specification. -/
def indexHashes (deref : Term → Term) (spec : Array Nat) (args : Array Term) : Array UInt64 :=
  spec.mapIdx fun i n =>
    if h : i < args.size then (if n > 0 then groundHash deref args[i] n else 0) else 0

def Clause.compile (c : Clause) : Clause :=
  { c with args := (match c.head with | .app _ as => as | _ => #[]), goals := flattenBody c.body }

def Key.ofTerm : Term → Key
  | .const c => .const c
  | .bound l => .bound l
  | .app (.const c) _ => .const c
  | .lit (.int i) => .int i
  | .lit (.str s) => .str s
  | _ => .flex

/-- Index key of the first argument of a head/goal. -/
def firstKey (t : Term) : Key :=
  match t with
  | .app _ as => if h : 0 < as.size then Key.ofTerm as[0] else .flex
  | _ => .flex

/-- The clauses of one predicate, in search order, with a first-argument index whose candidate
arrays are ready to use: the bucket of a key holds the clauses with that key and the clauses
with a variable first argument, in clause order. -/
structure PredDB where
  /-- Every clause, compiled, in search order. -/
  clauses : Array Clause := #[]
  byKey : Lean.PersistentHashMap Key (Array Clause) := {}
  /-- The clauses whose first argument is a variable: the candidates for a key with no bucket. -/
  flex : Array Clause := #[]
  /-- The `:index` specification: how deep each argument is indexed (0: not at all). Empty means
  the default, the first argument to depth one, which `byKey` answers by itself. -/
  spec : Array Nat := #[]
  deriving Inhabited

namespace PredDB

/-- Add a clause at the end. A clause with a variable first argument joins every bucket. -/
def push (db : PredDB) (c : Clause) : PredDB :=
  let c := c.compile
  let c := if db.spec.isEmpty then c else { c with ihash := indexHashes id db.spec c.args }
  let clauses := db.clauses.push c
  match firstKey c.head with
  | .flex =>
    let byKey := db.byKey.foldl (init := db.byKey) fun m k b => m.insert k (b.push c)
    { clauses, byKey, flex := db.flex.push c }
  | k => { db with clauses, byKey := db.byKey.insert k ((db.byKey.findD k db.flex).push c) }

/-- Build the index of a whole predicate at once, in time linear in the size of its buckets. -/
def ofArray (cs : Array Clause) (spec : Array Nat := #[]) : PredDB := Id.run do
  let cs := cs.map fun c =>
    let c := c.compile
    if spec.isEmpty then c else { c with ihash := indexHashes id spec c.args }
  let keys := cs.map (firstKey ·.head)
  -- positions of each key, ascending
  let mut pos : Std.HashMap Key (Array Nat) := {}
  let mut flexPos : Array Nat := #[]
  for i in [0:cs.size] do
    match keys[i]! with
    | .flex => flexPos := flexPos.push i
    | k => pos := pos.insert k ((pos.getD k #[]).push i)
  let mut byKey : Lean.PersistentHashMap Key (Array Clause) := {}
  for (k, ps) in pos.toList do
    -- ordered merge of the key's positions with the variable-headed ones
    let mut out : Array Clause := Array.mkEmpty (ps.size + flexPos.size)
    let mut i := 0
    let mut j := 0
    while i < ps.size || j < flexPos.size do
      if j ≥ flexPos.size || (i < ps.size && ps[i]! < flexPos[j]!) then
        out := out.push cs[ps[i]!]!; i := i + 1
      else
        out := out.push cs[flexPos[j]!]!; j := j + 1
    byKey := byKey.insert k out
  return { clauses := cs, byKey, flex := flexPos.map (cs[·]!), spec }

/-- Candidate clauses for a call whose first argument has key `k`, in clause order. Nothing is
built here: the array was prepared when the clauses were added. -/
-- @tg: implements:: [[openspec:elpi-core-engine#First-argument indexing]]
def candidates (db : PredDB) (k : Key) : Array Clause :=
  match k with
  | .flex => db.clauses
  | k => db.byKey.findD k db.flex

/-- Could the clause-head term `h` (clause variables `cvar` match anything) unify with the call
argument `g`, looking `n` levels deep? Only a clash between rigid constants, literals or
applications of constants rules a clause out; variables and λ-terms always stay possible, so
this never drops a clause that could apply. `deref` gives the head of the call's term. -/
partial def idxMatch (deref : Term → Term) (h g : Term) (n : Nat) : Bool :=
  if n == 0 then true else
  match h with
  | .cvar .. | .uvar .. | .lam _ | .bound _ => true
  | _ =>
    match deref g with
    | .uvar .. | .lam _ | .bound _ | .cvar .. => true
    | g' =>
      match h, g' with
      | .app (.const a) as, .app (.const b) bs =>
        a == b && as.size == bs.size && idxArgs deref as bs 0 (n - 1)
      | .const a, .const b => a == b
      | .lit a, .lit b => a == b
      | .app (.const _) _, .const _ | .const _, .app (.const _) _ => false
      | .app (.const _) _, .lit _ | .lit _, .app (.const _) _ => false
      | .const _, .lit _ | .lit _, .const _ => false
      | _, _ => true
where
  idxArgs (deref : Term → Term) (as bs : Array Term) (i n : Nat) : Bool :=
    if h : i < as.size then
      idxMatch deref as[i] bs[i]! n && idxArgs deref as bs (i + 1) n
    else true

/-- The candidate clauses for a call with arguments `args` (heads dereferenced by the caller):
with the default specification the first-argument bucket, otherwise the clauses whose indexed
arguments are all compatible with the call's, in clause order. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Deep and multi-argument indexing]]
def select (db : PredDB) (deref : Term → Term) (args : Array Term) (k : Key) : Array Clause :=
  if db.spec.isEmpty then db.candidates k
  else
    -- start from the first-argument bucket when the first argument is indexed
    let base := if db.spec[0]! ≥ 1 then db.candidates k else db.clauses
    let ghs := indexHashes deref db.spec args
    base.filter fun c => Id.run do
      for i in [0:db.spec.size] do
        let n := db.spec[i]!
        if n > 0 && i < c.args.size && i < args.size then
          let ch := c.ihash[i]!
          let gh := ghs[i]!
          -- both ground to the indexed depth: equal hashes are the same structure, different
          -- ones a rigid clash; otherwise compare the structures
          if ch != 0 && gh != 0 then
            if ch != gh then return false
          else if !idxMatch deref c.args[i]! args[i]! n then return false
      return true

end PredDB

/-- A clause with its grafting attributes, as produced by the loader. -/
structure ClauseItem where
  pred : ConstId
  clause : Clause
  before? : Option String := none
  after? : Option String := none

/-- Order the clauses of every predicate: source order, then grafting relative to named
clauses. Unknown and duplicate names are load errors. -/
-- @tg: implements:: [[openspec:elpi-core-engine#Clause names and grafting]]
def graft (items : Array ClauseItem) : Except ElpiError (Std.HashMap Nat (Array Clause)) := do
  -- phase 1: plain clauses in source order
  let mut lists : Std.HashMap Nat (Array Clause) := {}
  let mut names : Std.HashMap String Nat := {}   -- clause name -> predicate
  for it in items do
    if it.before?.isNone && it.after?.isNone then
      if let some n := it.clause.name? then
        if names.contains n then
          throw (.load s!"{it.clause.pos.toString}: duplicate clause name \"{n}\"")
        names := names.insert n it.pred.idx
      lists := lists.insert it.pred.idx ((lists.getD it.pred.idx #[]).push it.clause)
  -- phase 2: grafted clauses
  for it in items do
    let (anchor, isBefore) :=
      match it.before?, it.after? with
      | some n, _ => (some n, true)
      | none, some n => (some n, false)
      | none, none => (none, true)
    if let some a := anchor then
      let some p := names[a]?
        | throw (.load s!"{it.clause.pos.toString}: unknown clause name \"{a}\" in graft")
      if p != it.pred.idx then
        throw (.load s!"{it.clause.pos.toString}: grafted clause is not a clause of the predicate of \"{a}\"")
      if let some n := it.clause.name? then
        if names.contains n then
          throw (.load s!"{it.clause.pos.toString}: duplicate clause name \"{n}\"")
        names := names.insert n it.pred.idx
      let l := lists.getD p #[]
      let some idx := l.findIdx? (·.name? == some a)
        | throw (.load s!"unknown clause name \"{a}\"")
      let cut := if isBefore then idx else idx + 1
      lists := lists.insert p ((l.extract 0 cut).push it.clause ++ l.extract cut l.size)
  return lists

/-- The program database. -/
structure Database where
  preds : Lean.PersistentHashMap ConstId PredDB := {}
  deriving Inhabited

def Database.ofLists (lists : Std.HashMap Nat (Array Clause))
    (specs : Std.HashMap Nat (Array Nat) := {}) : Database :=
  { preds := lists.fold (init := {}) fun m p cs =>
      m.insert ⟨p⟩ (PredDB.ofArray cs (specs.getD p #[])) }

/-- Add a clause at the end of its predicate; the original database is untouched. -/
def Database.assert (db : Database) (p : ConstId) (c : Clause) : Database :=
  { preds := db.preds.insert p ((db.preds.findD p {}).push c) }

end Elpi
