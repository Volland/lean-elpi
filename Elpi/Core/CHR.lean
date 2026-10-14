import Elpi.Core.Store
import Elpi.Core.Unify

/-!
# CHR engine

Constraint Handling Rules: rule representation and head matching. Matching is one-way:
the rule's variables are fresh and assignable, every variable of the store is frozen
(`unifyMatch` with the store's variables protected), so a head can never assign a
variable of a stored constraint. Guards and bodies are run by the machine.
-/

-- @lat: [[components#CHR engine]]

namespace Elpi

/-- A compiled rule: heads, optional guard and body, with clause variables `cvar i`. -/
structure CHRRule where
  kept : Array Term
  removed : Array Term
  guard : Option Term
  body : Option Term
  nvars : Nat
  deriving Inhabited

/-- A `constraint P1 … Pn { rule … }` block. -/
structure ConstraintBlock where
  preds : Array ConstId
  rules : Array CHRRule
  deriving Inhabited

/-- Reserved index of `?-` is not fixed; heads of the form `(Ctx ?- C)` are recognised by
this constant, passed in by the machine. -/
structure CHRCtx where
  turnstile : Option ConstId

/-- Predicate a head constrains, looking through `(Ctx ?- C)`. -/
def headPred (ts : Option ConstId) : Term → Option ConstId
  | .app (.const c) #[_, inner] => if some c == ts then Unify.headConst inner else some c
  | .app (.const c) _ => some c
  | .const c => some c
  | _ => none

/-- Reify a recorded local program as a list of clause terms. -/
def reifyLocals (ls : Locals) : Term :=
  ls.foldr (fun lc acc => .app (.const ⟨12⟩) #[lc.term, acc]) (.const ⟨11⟩)

/-- One complete match of a rule: constraint ids per head (kept heads first) and the store
extended with the bindings of the rule's variables. -/
structure CHRMatch where
  ids : Array Nat
  store : Store
  vars : Array Term

/-- Match one head against one constraint in one-way mode; a head `(Ctx ?- C)` binds `Ctx`
to the recorded context of the constraint. -/
-- @tg: implements:: [[openspec:elpi-constraints#Scoped constraints]]
def matchHead (ts : Option ConstId) (s : Store) (boundary : Nat) (head : Term) (c : Constraint) :
    Option Store :=
  match head with
  | .app (.const k) #[ctx, inner] =>
    if some k == ts then
      (unifyMatch s boundary ctx (reifyLocals c.locals) c.depth).bind fun s' =>
        unifyMatch s' boundary inner c.goal c.depth
    else unifyMatch s boundary head c.goal c.depth
  | _ => unifyMatch s boundary head c.goal c.depth

/-- Depth-first search over the heads from position `j` on. -/
partial def matchHeads (ts : Option ConstId) (inst : Array Term) (boundary : Nat) (pos : Nat)
    (active : Constraint) (vars : Array Term) (j : Nat) (st : Store) (used ids : Array Nat) :
    List CHRMatch :=
  if j < inst.size then
    if j == pos then matchHeads ts inst boundary pos active vars (j + 1) st used (ids.push active.id)
    else
      match headPred ts inst[j]! with
      | none => []
      | some p =>
        let cands := st.cstore.byPred.findD p.idx #[]
        cands.toList.flatMap fun cid =>
          if used.contains cid then []
          else
            match st.cstore.find? cid with
            | none => []
            | some c =>
              match matchHead ts st boundary inst[j]! c with
              | some st' =>
                matchHeads ts inst boundary pos active vars (j + 1) st' (used.push cid) (ids.push cid)
              | none => []
  else [{ ids, store := st, vars }]

/-- All matches of `rule` in which the head at position `pos` (counting kept heads first)
is the active constraint, partners taken from the predicate index in insertion order. -/
-- @tg: implements:: [[openspec:elpi-constraints#CHR rules]]
def matchRule (ts : Option ConstId) (rule : CHRRule) (s : Store) (active : Constraint)
    (pos : Nat) : List CHRMatch := Id.run do
  let heads := rule.kept ++ rule.removed
  let boundary := s.nextVar
  -- fresh rule variables at the level of the active constraint
  let mut st := s
  let mut vars : Array Term := #[]
  for _ in [0:rule.nvars] do
    let (u, st') := st.fresh active.depth
    st := st'
    vars := vars.push (.uvar u #[])
  let inst := heads.map (Term.renameCVars vars active.depth)
  let some h0 := inst[pos]? | return []
  let some st0 := matchHead ts st boundary h0 active | return []
  return matchHeads ts inst boundary pos active vars 0 st0 #[active.id] #[]

end Elpi
