import Elpi.Lean.Tactic

/-!
# The `elpi_derive` command

`elpi_derive <Class> <Type>` runs the ELPI derivers of `lean.derive` (BEq, DecidableEq,
Repr). The command is defined with the same `elpi_program` / `elpi_command` / `elpi_export`
machinery that user code has.
-/

-- @lat: [[components#Commands]]

open Elpi.Cmd

elpi_program elpiDeriveProg
elpi_accumulate elpiDeriveProg lp%{ accumulate lean.derive. }%
elpi_command elpi_derive := elpiDeriveProg
elpi_export elpi_derive
