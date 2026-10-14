import TestUtil
import Lean
open Elpi.Cmd

elpi_program mytac
elpi_accumulate mytac lp%{
  accumulate lean.
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ Pf {{True}}) _ [] :- Pf = {{True.intro}}.
}%
elpi_tactic mytac := mytac

-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#solve assigns the goal metavariable]]
example : True := by elpi mytac

elpi_program badtac
elpi_accumulate badtac lp%{
  accumulate lean.
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ Pf {{True}}) _ [] :- Pf = {{(0 : Nat)}}.
}%
elpi_tactic badtac := badtac

-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#Ill-typed proof is rejected]]
/-- error: type mismatch
  0
has type
  Nat
but is expected to have type
  True -/
#guard_msgs (whitespace := lax) in
example : True := by elpi badtac

elpi_program splittac
elpi_accumulate splittac lp%{
  accumulate lean.
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal Ctx Pf {{ lp:{{P}} ∧ lp:{{Q}} }}) _ [goal Ctx A P, goal Ctx B Q] :-
    Pf = {{And.intro lp:{{A}} lp:{{B}}}}.
}%
elpi_tactic split_tac := splittac

-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#Remaining goals are returned to Lean]]
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  elpi split_tac
  all_goals assumption
