import LeanHost.Program.A
import TestUtil
open Elpi.Cmd

-- @tg: verifies:: [[openspec:lean-integration#Program and database declarations#Program persists across imports]]
/-- info: X = b -/
#guard_msgs in
#elpi myprog lp%{ edge a X }%

-- @tg: verifies:: [[openspec:lean-integration#Program and database declarations#Database extended downstream]]
elpi_accumulate myprog.db lp%{ known 2. }%

set_option elpi.solutions 5 in
/-- info: X = 1
---
info: X = 2 -/
#guard_msgs in
#elpi myprog lp%{ known X }%
