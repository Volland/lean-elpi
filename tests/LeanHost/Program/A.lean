import Elpi
open Elpi.Cmd

elpi_program myprog
elpi_accumulate myprog file "rules.elpi"

elpi_db myprog.db
elpi_accumulate myprog.db lp%{ pred known o:int. known 1. }%
elpi_accumulate myprog db myprog.db

/-- info: X = b -/
#guard_msgs in
#elpi myprog lp%{ edge a X }%

set_option elpi.solutions 5 in
/-- info: X = 1 -/
#guard_msgs in
#elpi myprog lp%{ known X }%
