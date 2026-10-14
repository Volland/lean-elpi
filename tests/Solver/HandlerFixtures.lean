import Elpi

/-! The `"lia"` fixture handler (tier T3): upper bounds `lia.le X k`; it keeps the strongest
bound per variable and checks bounds when the variable is instantiated. -/

open Elpi

structure LiaState where
  adds : Nat

deriving instance TypeName for LiaState

private def bound? (hs : HStore) (c : Constraint) : Option (Term × Int) :=
  match hs.deref c.goal with
  | .app _ #[x, k] =>
    match hs.deref k with
    | .lit (.int n) => some (hs.deref x, n)
    | _ => none
  | _ => none

@[elpi_constraint_handler "lia"]
def liaHandler : ConstraintHandler where
  keys := ["lia.le"]
  init := Dynamic.mk (LiaState.mk 0)
  onAdd c hs :=
    match bound? hs c with
    | none => .keep
    | some (x, k) =>
      match hs.owned.find? fun o => (bound? hs o).any fun (y, _) => y == x with
      | some o =>
        let k0 := ((bound? hs o).map (·.2)).getD k
        -- keep only the stronger bound
        .simplify (hs.owned.filter (·.id != o.id) ++ [if k < k0 then c else o])
      | none => .keep
  onWake u hs :=
    let mine := hs.owned.filter fun o => o.keys.contains u
    let ok := mine.all fun o =>
      match bound? hs o with
      | some (.lit (.int v), k) => v ≤ k
      | _ => true
    if ok then .simplify (hs.owned.filter fun o => !o.keys.contains u) else .fail
