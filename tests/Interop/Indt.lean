import TestUtil
import Lean
open Elpi.Cmd Lean

-- An ELPI command that reads `Option` with `lean.env.indt`, renames it and adds the copy:
-- the Lean analogue of Coq-Elpi's `coq.env.indt` / `coq.env.add-indt`.
elpi_program cloner
elpi_accumulate cloner lp%{
  accumulate lean.
  pred main i:list argument.
  pred rename-ctor i:string, i:string, i:lean.ctor, o:lean.ctor.
  rename-ctor From To (lean.ctor CN T) (lean.ctor CN1 T1) :-
    lean.name->string CN CS,
    L is size From, N is size CS, M is N - L, Rest is substring CS L M,
    CS1 is To ^ Rest,
    lean.string->name CS1 CN1,
    copy T T1.
  main [str From, str To] :-
    lean.string->name From FN, lean.string->name To TN,
    lean.env.indt FN (lean.indt _ NP NI Ty Cs),
    ( pi L\ copy (const FN L) (const TN L) ) => (
      copy Ty Ty1,
      std.map Cs (rename-ctor From To) Cs1 ),
    lean.add_inductive (lean.indt TN NP NI Ty1 Cs1).
}%
elpi_command clone := cloner
elpi_export clone

-- @tg: verifies:: [[openspec:lean-interop#Inductive types from ELPI#Copy of an inductive type]]
clone "Option" "MyOption"

#check @MyOption.some
#check @MyOption.casesOn
example : MyOption Nat := MyOption.some 3
def MyOption.get (d : Nat) : MyOption Nat → Nat
  | .none => d
  | .some x => x
example : (MyOption.some 3).get 0 = 3 := rfl

-- @tg: verifies:: [[openspec:lean-interop#Inductive types from ELPI#Phase restriction]]
elpi_program badind
elpi_accumulate badind lp%{
  accumulate lean.
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ _ _) _ _ :- lean.string->name "Nope" N, lean.add_inductive (lean.indt N 0 0 {{Type}} []).
}%
elpi_tactic badind_tac := badind

/-- error: tactic badind_tac failed: lean.add_inductive is only available in commands (current phase: tactic) -/
#guard_msgs in
example : True := by elpi badind_tac
