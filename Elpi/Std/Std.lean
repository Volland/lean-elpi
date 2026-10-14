/-!
# Standard library

The clean-room `std` library and the builtin prelude, embedded in the compiled artefact
with `include_str` so binaries need no `lib/elpi/` directory on disk.
-/

-- @lat: [[components#Standard library]]

namespace Elpi.Std

/-- Types of control constructs and core builtins. -/
def builtinSource : String := include_str "../../lib/elpi/builtin.elpi"

/-- The ELPI-side standard library (`std.*`). -/
-- @tg: implements:: [[openspec:elpi-libraries#Standard library]]
def source : String := include_str "../../lib/elpi/std.elpi"

/-- The `leq` CHR solver (tier T1), loaded with `accumulate leq.` -/
-- @tg: implements:: [[openspec:elpi-solver-api#CHR solvers in ELPI]]
def leqSource : String := include_str "../../lib/elpi/leq.elpi"

/-- Libraries embedded in the binary, by accumulate name. -/
-- @tg: implements:: [[openspec:elpi-libraries#Embedded libraries]]
def embedded : List (String × String) :=
  [("std", source), ("builtin", builtinSource), ("leq", leqSource)]

end Elpi.Std
-- rebuild marker: bump when lib/elpi/*.elpi change (include_str is not tracked by Lake)
-- rebuild marker 2
-- rebuild marker 3
