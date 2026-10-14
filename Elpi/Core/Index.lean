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

/-- Interned constants: the first entries are reserved for control constructs. -/
structure Symbols where
  names : Array String := #[]
  ids : Std.HashMap String Nat := {}
  deriving Inhabited

def Symbols.intern (s : Symbols) (n : String) : ConstId × Symbols :=
  match s.ids[n]? with
  | some i => (⟨i⟩, s)
  | none => (⟨s.names.size⟩, { names := s.names.push n, ids := s.ids.insert n s.names.size })

def Symbols.find? (s : Symbols) (n : String) : Option ConstId := (s.ids[n]?).map (⟨·⟩)

def Symbols.name (s : Symbols) (c : ConstId) : String := s.names[c.idx]!

def reservedNames : Array String :=
  #["true", "fail", "!", ",", ";", "=>", "pi", "sigma", "=", "not", ":-", "[]", "::",
    "findall_solutions", "->", "<=", "halt", "print", "some", "none", "pr", "tt", "ff", "?-", "declare_constraint"]

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

def Symbols.initial : Symbols :=
  reservedNames.foldl (fun s n => (s.intern n).2) {}

/-- A compiled clause; `cvar i` ranges over `i < nvars`. -/
structure Clause where
  head : Term
  body : Term
  nvars : Nat
  name? : Option String := none
  pos : Pos := {}
  deriving Inhabited

/-- First-argument key of a clause head or of a call. -/
inductive Key where
  | const (c : ConstId)
  | int (i : Int)
  | str (s : String)
  | flex
  deriving BEq, Hashable, Inhabited

def Key.ofTerm : Term → Key
  | .const c => .const c
  | .app (.const c) _ => .const c
  | .lit (.int i) => .int i
  | .lit (.str s) => .str s
  | _ => .flex

/-- Index key of the first argument of a head/goal. -/
def firstKey (t : Term) : Key :=
  match t with
  | .app _ as => if h : 0 < as.size then Key.ofTerm as[0] else .flex
  | _ => .flex

/-- The clauses of one predicate, in search order, with a first-argument index. -/
structure PredDB where
  clauses : Array Clause := #[]
  byKey : Lean.PersistentHashMap Key (Array Nat) := {}
  flex : Array Nat := #[]
  deriving Inhabited

namespace PredDB

def push (db : PredDB) (c : Clause) : PredDB :=
  let i := db.clauses.size
  let k := firstKey c.head
  let db := { db with clauses := db.clauses.push c }
  match k with
  | .flex => { db with flex := db.flex.push i }
  | k => { db with byKey := db.byKey.insert k ((db.byKey.findD k #[]).push i) }

/-- Ordered merge of two ascending index arrays. -/
def merge (a b : Array Nat) : Array Nat := Id.run do
  let mut out := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size || (i < a.size && a[i]! < b[j]!) then
      out := out.push a[i]!; i := i + 1
    else
      out := out.push b[j]!; j := j + 1
  return out

/-- Candidate clause positions for a call whose first argument has key `k`: the bucket of
`k` merged with the variable clauses, in clause order. -/
-- @tg: implements:: [[openspec:elpi-core-engine#First-argument indexing]]
def candidates (db : PredDB) (k : Key) : Array Nat :=
  match k with
  | .flex => Array.range db.clauses.size
  | k => merge (db.byKey.findD k #[]) db.flex

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

def Database.ofLists (lists : Std.HashMap Nat (Array Clause)) : Database :=
  { preds := lists.fold (init := {}) fun m p cs =>
      m.insert ⟨p⟩ (cs.foldl PredDB.push {}) }

/-- Add a clause at the end of its predicate; the original database is untouched. -/
def Database.assert (db : Database) (p : ConstId) (c : Clause) : Database :=
  { preds := db.preds.insert p ((db.preds.findD p {}).push c) }

end Elpi
