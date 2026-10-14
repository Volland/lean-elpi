import TestUtil
import Lean
open Elpi.Cmd

elpi_program badp
elpi_accumulate badp lp%{
  accumulate lean.
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ Pf {{True}}) _ [] :-
    lean.string->name "Sneaky" N,
    lean.add_decl (lean.def N {{Nat}} {{(0 : Nat)}}),
    Pf = {{True.intro}}.
}%
elpi_tactic bad_tac := badp

-- @tg: verifies:: [[openspec:lean-integration#Phase-restricted effects#Declaration added from a tactic is rejected]]
/-- error: tactic bad_tac failed: lean.add_decl is only available in commands (current phase: tactic) -/
#guard_msgs in
example : True := by elpi bad_tac

/-- error: Unknown identifier `Sneaky` -/
#guard_msgs in
#check Sneaky
