import Lean.Data.Json
import Elpi.Core.Parser

/-!
# Host API types

The stable values a host program exchanges with the engine: declared types and modes of a
predicate (`TyTerm`, `Arg`, `PredSig`), arguments of a goal built from terms (`GoalArg`) and
solution terms (`ResultTerm`) with their JSON form. Nothing here refers to the engine's internal
term or type representations, so they can change without breaking hosts.
-/

-- @lat: [[components#Host API]]

namespace Elpi.Host

open Lean (Json JsonNumber)

/-! ### Types and signatures -/

/-- A declared type: kind constants, type applications, arrows and type variables (by their
declared name). -/
inductive TyTerm where
  | const (name : String)
  | app (head : String) (args : List TyTerm)
  | arrow (dom cod : TyTerm)
  | var (name : String)
  deriving Repr, Inhabited

namespace TyTerm

mutual
def beq : TyTerm → TyTerm → Bool
  | .const a, .const b => a == b
  | .app h as, .app k bs => h == k && beqList as bs
  | .arrow a b, .arrow c d => beq a c && beq b d
  | .var a, .var b => a == b
  | _, _ => false
def beqList : List TyTerm → List TyTerm → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

instance : BEq TyTerm := ⟨beq⟩

mutual
theorem beq_iff_eq' : (a b : TyTerm) → beq a b = true ↔ a = b
  | .const a, .const b => by simp [beq]
  | .app h as, .app k bs => by simp [beq, beqList_iff_eq as bs]
  | .arrow a b, .arrow c d => by simp [beq, beq_iff_eq' a c, beq_iff_eq' b d]
  | .var a, .var b => by simp [beq]
  | .const _, .app .. | .const _, .arrow .. | .const _, .var _
  | .app .., .const _ | .app .., .arrow .. | .app .., .var _
  | .arrow .., .const _ | .arrow .., .app .. | .arrow .., .var _
  | .var _, .const _ | .var _, .app .. | .var _, .arrow .. => by simp [beq]
theorem beqList_iff_eq : (as bs : List TyTerm) → beqList as bs = true ↔ as = bs
  | [], [] => by simp [beqList]
  | a :: as, b :: bs => by simp [beqList, beq_iff_eq' a b, beqList_iff_eq as bs]
  | [], _ :: _ | _ :: _, [] => by simp [beqList]
end

/-- Comparing signatures with `==` agrees with equality. -/
-- @tg: verifies:: [[openspec:elpi-host-api#Predicate signature lookup]]
theorem beq_iff_eq {a b : TyTerm} : (a == b) = true ↔ a = b := beq_iff_eq' a b

instance : LawfulBEq TyTerm where
  eq_of_beq h := beq_iff_eq.mp h
  rfl := beq_iff_eq.mpr rfl

instance : DecidableEq TyTerm := fun a b =>
  if h : (a == b) = true then isTrue (beq_iff_eq.mp h) else isFalse fun e => h (beq_iff_eq.mpr e)

partial def toString : TyTerm → String
  | .const n => n
  | .app h as => "(" ++ " ".intercalate (h :: as.map toString) ++ ")"
  | .arrow a b =>
    let l := match a with | .arrow .. => "(" ++ a.toString ++ ")" | _ => a.toString
    l ++ " -> " ++ b.toString
  | .var n => n

instance : ToString TyTerm := ⟨toString⟩

end TyTerm

/-- One argument of a predicate: its mode and its declared type. -/
structure Arg where
  mode : Mode
  ty : TyTerm
  deriving Repr, Inhabited, BEq

/-- The declared signature of a predicate. -/
structure PredSig where
  name : String
  args : Array Arg
  deriving Repr, Inhabited, BEq

/-! ### Result terms -/

/-- A solution term: constants, applications of a constant, literals and lists, plus markers
for what a host cannot read as data (an unbound variable, a λ-abstraction, opaque host data).
A float is kept as its IEEE-754 bits, so it round-trips exactly. -/
inductive ResultTerm where
  | const (name : String)
  | app (head : String) (args : Array ResultTerm)
  | int (value : Int)
  | float (bits : UInt64)
  | str (value : String)
  | list (items : Array ResultTerm)
  | unbound
  | lam
  | opaque (typeName : String) (data : String)
  deriving Repr, Inhabited, BEq

namespace ResultTerm

def ofFloat (f : Float) : ResultTerm := .float f.toBits

/-- The float of a `float` term. -/
def toFloat? : ResultTerm → Option Float
  | .float b => some (Float.ofBits b)
  | _ => none

/-! The JSON form is a tagged array, `["app", "person", [["int", 42]]]`; a float carries its
bits as an integer. -/

mutual
def toJson : ResultTerm → Json
  | .const n => .arr #[.str "const", .str n]
  | .app h ⟨args⟩ => .arr #[.str "app", .str h, .arr ⟨toJsonList args⟩]
  | .int i => .arr #[.str "int", .num ⟨i, 0⟩]
  | .float b => .arr #[.str "float", .num ⟨b.toNat, 0⟩]
  | .str s => .arr #[.str "str", .str s]
  | .list ⟨xs⟩ => .arr #[.str "list", .arr ⟨toJsonList xs⟩]
  | .unbound => .arr #[.str "unbound"]
  | .lam => .arr #[.str "lam"]
  | .opaque t d => .arr #[.str "opaque", .str t, .str d]
def toJsonList : List ResultTerm → List Json
  | [] => []
  | x :: xs => toJson x :: toJsonList xs
end

mutual
def fromJson? : Json → Option ResultTerm
  | .arr ⟨[.str "const", .str n]⟩ => some (.const n)
  | .arr ⟨[.str "app", .str h, .arr ⟨args⟩]⟩ => (fromJsonList? args).map fun as => .app h ⟨as⟩
  | .arr ⟨[.str "int", .num ⟨i, 0⟩]⟩ => some (.int i)
  | .arr ⟨[.str "float", .num ⟨b, 0⟩]⟩ =>
    if b.toNat < UInt64.size then some (.float (UInt64.ofNat b.toNat)) else none
  | .arr ⟨[.str "str", .str s]⟩ => some (.str s)
  | .arr ⟨[.str "list", .arr ⟨xs⟩]⟩ => (fromJsonList? xs).map fun as => .list ⟨as⟩
  | .arr ⟨[.str "unbound"]⟩ => some .unbound
  | .arr ⟨[.str "lam"]⟩ => some .lam
  | .arr ⟨[.str "opaque", .str t, .str d]⟩ => some (.opaque t d)
  | _ => none
def fromJsonList? : List Json → Option (List ResultTerm)
  | [] => some []
  | j :: js => do return (← fromJson? j) :: (← fromJsonList? js)
end

mutual
/-- Decoding the JSON form of a term gives the term back. -/
-- @tg: verifies:: [[openspec:elpi-host-api#Structured solution terms#JSON form round-trips]]
theorem json_roundtrip : (t : ResultTerm) → fromJson? (toJson t) = some t
  | .const n => by simp [toJson, fromJson?]
  | .app h ⟨args⟩ => by simp [toJson, fromJson?, json_roundtrip_list args]
  | .int i => by simp [toJson, fromJson?]
  | .float b => by simp [toJson, fromJson?, UInt64.toNat_lt_size]
  | .str s => by simp [toJson, fromJson?]
  | .list ⟨xs⟩ => by simp [toJson, fromJson?, json_roundtrip_list xs]
  | .unbound => by simp [toJson, fromJson?]
  | .lam => by simp [toJson, fromJson?]
  | .opaque t d => by simp [toJson, fromJson?]
theorem json_roundtrip_list : (xs : List ResultTerm) → fromJsonList? (toJsonList xs) = some xs
  | [] => by simp [toJsonList, fromJsonList?]
  | x :: xs => by simp [toJsonList, fromJsonList?, json_roundtrip x, json_roundtrip_list xs]
end

partial def toString : ResultTerm → String
  | .const n => n
  | .app h args => "(" ++ " ".intercalate (h :: args.toList.map toString) ++ ")"
  | .int i => s!"{i}"
  | .float b => s!"{Float.ofBits b}"
  | .str s => s.quote
  | .list xs => "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"
  | .unbound => "_"
  | .lam => "<lambda>"
  | .opaque t _ => s!"<{t}>"

instance : ToString ResultTerm := ⟨toString⟩

end ResultTerm

/-- An argument of a goal built from terms: an input value or a named output variable. -/
inductive GoalArg where
  | value (t : ResultTerm)
  | out (name : String)
  deriving Repr, Inhabited

/-- A parse or type error inside one source unit. Lines count from 1 and columns from 0, as in
Lean positions. -/
structure Diagnostic where
  unit : String
  line : Nat
  col : Nat
  msg : String
  deriving Repr, Inhabited, BEq

def Diagnostic.ofPos (p : Pos) (msg : String) : Diagnostic :=
  { unit := p.file, line := p.line, col := p.col, msg }

/-- Errors of the host API. Argument and row numbers count from 1. -/
inductive Error where
  /-- Parse or type errors located in the source units. -/
  | located (diags : List Diagnostic)
  | unknownPred (name : String)
  /-- An argument of a goal does not fit the predicate's signature (index 0: the goal as a whole). -/
  | argument (pred : String) (index : Nat) (msg : String)
  /-- An argument of a fact in a batch does not fit the predicate's signature. -/
  | fact (pred : String) (row index : Nat) (msg : String)
  | engine (e : ElpiError)
  deriving Inhabited

def Error.toString : Error → String
  | .located ds => "\n".intercalate (ds.map fun d => s!"{d.unit}:{d.line}:{d.col}: {d.msg}")
  | .unknownPred n => s!"unknown predicate '{n}'"
  | .argument p 0 m => s!"goal {p}: {m}"
  | .argument p i m => s!"goal {p}, argument {i}: {m}"
  | .fact p r i m => s!"fact {p}, row {r}, argument {i}: {m}"
  | .engine e => e.toString

instance : ToString Error := ⟨Error.toString⟩

end Elpi.Host
