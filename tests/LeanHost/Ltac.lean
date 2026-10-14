import TestUtil
import Lean
open Elpi.Cmd

elpi_program iaprog
elpi_accumulate iaprog lp%{
  accumulate lean.ltac.
  pred solve i:goal, i:list argument, o:list goal.
  solve G _ Gs :- lean.ltac.then (lean.ltac.intro "h") lean.ltac.assumption G Gs.
}%
elpi_tactic intro_assume := iaprog

-- @tg: verifies:: [[openspec:elpi-libraries#Tactic combinator library#then composes two tactics]]
theorem intro_ok (p : Prop) : p → p := by elpi intro_assume

#print intro_ok

elpi_program orprog
elpi_accumulate orprog lp%{
  accumulate lean.ltac.
  pred solve i:goal, i:list argument, o:list goal.
  solve G _ Gs :- lean.ltac.orelse (lean.ltac.exact {{(0 : Nat)}}) lean.ltac.assumption G Gs.
}%
elpi_tactic or_tac := orprog

-- @tg: verifies:: [[openspec:elpi-libraries#Tactic combinator library#orelse falls back on failure]]
example (p : Prop) (hp : p) : p := by elpi or_tac

elpi_program applyprog
elpi_accumulate applyprog lp%{
  accumulate lean.ltac.
  pred solve i:goal, i:list argument, o:list goal.
  solve G [trm F] Gs :- lean.ltac.apply F G Gs.
}%
elpi_tactic apply_tac := applyprog

example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  elpi apply_tac hpq
  assumption
