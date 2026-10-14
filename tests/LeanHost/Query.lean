import TestUtil
import Lean
open Elpi.Cmd

elpi_program myprog
elpi_accumulate myprog lp%{ accumulate lean. }%

-- @tg: verifies:: [[openspec:lean-integration#Query command#Solutions are shown in the infoview]]
/-- info: L = [1, 2] -/
#guard_msgs in
#elpi myprog lp%{ std.append [1] [2] L }%

/-- info: T = {{Nat → Nat}} -/
#guard_msgs in
#elpi myprog lp%{ lean.infer {{Nat.succ}} T }%

-- @tg: verifies:: [[openspec:lean-integration#Query command#Failure is reported]]
/-- error: query has no solution -/
#guard_msgs in
#elpi myprog lp%{ std.mem [1, 2] 3 }%
