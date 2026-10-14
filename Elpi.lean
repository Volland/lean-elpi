import Elpi.Core.Builtins
import Elpi.Core.CHR
import Elpi.Core.Constraints
import Elpi.Core.Index
import Elpi.Core.Machine
import Elpi.Core.Parser
import Elpi.Core.Store
import Elpi.Core.Term
import Elpi.Core.Typecheck
import Elpi.Core.Unify
import Elpi.LF.Check
import Elpi.LF.Export
import Elpi.LF.ProofTerm
import Elpi.LF.Strategy
import Elpi.Lean.Builtins
import Elpi.Lean.Commands
import Elpi.Lean.Derive
import Elpi.Lean.Libraries
import Elpi.Lean.Marshal
import Elpi.Lean.Quote
import Elpi.Lean.Reflect
import Elpi.Lean.Tactic
import Elpi.Runtime.Api
import Elpi.Runtime.Dsl
import Elpi.Solver.Registry
import Elpi.Std.Std

/-!
# LeanElpi

A clean-room Lean 4 implementation of the ELPI dialect of λProlog. Architecture and
design: `tg.md/` (start at `tg.md/overview.md`); requirements: `openspec/changes/`.
-/

-- @lat: [[architecture#Module map]]
