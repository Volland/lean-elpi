import TestUtil
import Lean
open Elpi.Cmd

elpi_program cmdprog
elpi_accumulate cmdprog lp%{
  accumulate lean.
  pred main i:list argument.
  % define a constant named after the string argument whose value is the numeral argument
  main [trm (const _ _), int I, str S] :-
    lean.string->name S N,
    lean.add_decl (lean.def N {{Nat}} (lit (nat I))).
}%
elpi_command mycmd := cmdprog
elpi_export mycmd

-- @tg: verifies:: [[openspec:lean-integration#ELPI commands and export#Exported command parses its arguments]]
mycmd Nat.succ 3 "answer"

example : answer = 3 := rfl
