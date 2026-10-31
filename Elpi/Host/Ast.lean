import Elpi.Host.Types

/-!
# Public clause AST

A read-only view of a program's source: its `kind`, `type` and `pred` declarations, its
`accumulate` directives, and every clause with its head, a classified body and its position.
Body goals tell conjunction, disjunction, negation, cut, `pi`, `sigma`, implication, predicate
calls and builtin calls apart, which is what rule analyses (stratification, scope, staging) need.
The view is built from the parsed form and versioned with LeanElpi's minor version; the engine's
internal clause representation stays private.
-/

-- @lat: [[components#Host API]]

namespace Elpi.Host.Ast

/-- A term of the source, with variables and λ-binders by name. -/
inductive Term where
  | const (name : String)
  | var (name : String)
  | int (value : Int)
  | float (value : Float)
  | str (value : String)
  | app (head : Term) (args : List Term)
  | lam (binder : String) (body : Term)
  deriving Repr, Inhabited

mutual
/-- A classified body goal. -/
inductive Goal where
  | true
  | fail
  | cut
  | conj (goals : List Goal)
  | disj (left right : Goal)
  /-- `not G` or `\+ G`. -/
  | not (goal : Goal)
  | pi (binder : String) (body : Goal)
  | sigma (binder : String) (body : Goal)
  /-- `H => G`: the hypothetical clauses `H` hold while `G` runs. -/
  | impl (hyps : List Hyp) (body : Goal)
  /-- A call of a predicate defined by clauses (or not defined at all). -/
  | call (pred : String) (args : List Term)
  /-- A call of a builtin predicate. -/
  | builtin (name : String) (args : List Term)
  /-- A goal whose head is not a constant, such as a variable. -/
  | other (t : Term)
  deriving Repr, Inhabited

/-- A hypothetical clause of an implication goal. -/
inductive Hyp where
  | mk (head : Term) (body : Goal)
  deriving Repr, Inhabited
end

/-- The predicate a clause head defines, if its head is a constant. -/
def headPred? : Term → Option String
  | .const n => some n
  | .app (.const n) _ => some n
  | _ => none

def Hyp.head : Hyp → Term | .mk h _ => h
def Hyp.body : Hyp → Goal | .mk _ b => b
def Hyp.pred? (h : Hyp) : Option String := headPred? h.head

/-- A clause of the program. -/
structure Clause where
  /-- The defined predicate. -/
  pred : String
  head : Term
  body : Goal
  name? : Option String := none
  pos : Pos
  deriving Repr, Inhabited

/-- The public view of a program's source units. -/
structure Program where
  /-- Kind declarations with their arity. -/
  kinds : Array (String × Nat) := #[]
  /-- `type` declarations of constants, with the declared type. -/
  types : Array (String × TyTerm) := #[]
  /-- `pred` declarations, with modes. -/
  preds : Array PredSig := #[]
  /-- `accumulate` directives, in order. -/
  accumulates : Array String := #[]
  /-- The clauses of the units themselves (not of accumulated libraries), in order. -/
  clauses : Array Clause := #[]
  deriving Inhabited

/-! ### Building the view -/

partial def termOf : STm → Term
  | .const n _ => .const n
  | .var n _ => .var n
  | .int i _ => .int i
  | .float f _ => .float f
  | .str s _ => .str s
  | .app f args _ => .app (termOf f) (args.map termOf)
  | .lam x b _ => .lam x (termOf b)
  | .spill g _ => termOf g
  | .quote t _ => .const s!"\{\{{t}}}"
  | .term _ _ _ _ => .const "<lean term>"

def callOf (builtins : Std.HashSet String) (n : String) (args : List Term) : Goal :=
  if builtins.contains n then .builtin n args else .call n args

mutual
/-- Classify a goal; `builtins` names the predicates implemented natively. -/
partial def goalOf (builtins : Std.HashSet String) : STm → Goal
  | .const "true" _ => .true
  | .const "fail" _ => .fail
  | .const "!" _ => .cut
  | .app (.const "," _) gs _ => .conj (gs.foldr (fun g acc => conjuncts builtins g ++ acc) [])
  | .app (.const ";" _) [a, b] _ => .disj (goalOf builtins a) (goalOf builtins b)
  | .app (.const "not" _) [g] _ | .app (.const "\\+" _) [g] _ => .not (goalOf builtins g)
  | .app (.const "pi" _) [.lam x b _] _ => .pi x (goalOf builtins b)
  | .app (.const "sigma" _) [.lam x b _] _ => .sigma x (goalOf builtins b)
  | .app (.const "=>" _) [h, b] _ => .impl (hypsOf builtins h) (goalOf builtins b)
  | .app (.const "<=" _) [b, h] _ => .impl (hypsOf builtins h) (goalOf builtins b)
  | .const n _ => callOf builtins n []
  | .app (.const n _) args _ => callOf builtins n (args.map termOf)
  | .spill g _ => goalOf builtins g
  | t => .other (termOf t)

partial def conjuncts (builtins : Std.HashSet String) (g : STm) : List Goal :=
  match goalOf builtins g with
  | .conj gs => gs
  | g' => [g']

/-- The clauses of an implication's left side: one clause, a conjunction or a list of them. -/
partial def hypsOf (builtins : Std.HashSet String) : STm → List Hyp
  | .app (.const "," _) hs _ => hs.flatMap (hypsOf builtins)
  | .app (.const "::" _) [h, rest] _ => hypsOf builtins h ++ hypsOf builtins rest
  | .const "[]" _ => []
  | .app (.const ":-" _) [h, b] _ => [.mk (termOf h) (goalOf builtins b)]
  | .app (.const "pi" _) [.lam _ b _] _ => hypsOf builtins b
  | h => [.mk (termOf h) .true]
end

/-- One clause as the view: head, classified body, name and position. -/
def clauseOf (builtins : Std.HashSet String) (attrs : Attrs) (t : STm) (pos : Pos) :
    Option Clause :=
  let (h, b) := match t with
    | .app (.const ":-" _) [h, b] _ => (h, some b)
    | t => (t, none)
  let head := termOf h
  (headPred? head).map fun pred =>
    { pred, head, body := (b.map (goalOf builtins)).getD .true, name? := attrs.name, pos }

/-- The `accumulate` directives of a parsed unit, including those inside namespaces. -/
partial def accumulatesOf : List Decl → List String
  | [] => []
  | .accumulate f _ :: ds => f :: accumulatesOf ds
  | .ns _ inner _ :: ds => accumulatesOf inner ++ accumulatesOf ds
  | _ :: ds => accumulatesOf ds

end Elpi.Host.Ast
