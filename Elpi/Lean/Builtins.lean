import Lean.Meta.Basic
import Elpi.Core.Builtins

/-!
# Lean builtins

The `MetaM` host-monad instance: a choice point snapshots the full `Meta.SavedState`, so
backtracking rewinds metavariable assignments and the message log together with ELPI
bindings. This is the only module of the engine that depends on `Lean.Meta`; the core
(`Elpi/Core/*`) must not import it. M3 adds the Lean-specific builtins here.
-/

-- @lat: [[components#Lean builtins]]

namespace Elpi.Host

open Lean Meta

-- @tg: implements:: [[openspec:elpi-core-engine#Monad-generic engine]]
instance : Elpi.Backtrackable MetaM Meta.SavedState :=
  ⟨Meta.saveState, fun s => s.restore⟩

instance : Elpi.Output MetaM := ⟨fun s => IO.print s⟩

end Elpi.Host
