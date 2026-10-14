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

/-- The Lean API library: reflection types, tactic interface, `lean.*` signatures. -/
-- @tg: implements:: [[openspec:elpi-libraries#Lean API library]]
def leanSource : String := include_str "../../lib/elpi/lean.elpi"

/-- Tactic combinators (`accumulate lean.ltac.`). -/
-- @tg: implements:: [[openspec:elpi-libraries#Tactic combinator library]]
def ltacSource : String := include_str "../../lib/elpi/lean.ltac.elpi"

/-- ELPI derivers (`accumulate lean.derive.`). -/
-- @tg: implements:: [[openspec:elpi-libraries#Derive library]]
def deriveSource : String := include_str "../../lib/elpi/lean.derive.elpi"

/-- Libraries embedded in the binary, by accumulate name. -/
-- @tg: implements:: [[openspec:elpi-libraries#Embedded libraries]]
def embedded : List (String × String) :=
  [("std", source), ("builtin", builtinSource), ("leq", leqSource), ("lean", leanSource), ("lean.ltac", ltacSource), ("lean.derive", deriveSource)]

end Elpi.Std
-- rebuild marker: bump when lib/elpi/*.elpi change (include_str is not tracked by Lake)
-- rebuild marker 2
-- rebuild marker 3
-- rebuild marker 4
-- rebuild marker 5
-- rebuild marker 6
-- rebuild marker 7
