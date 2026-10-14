/-!
# LF strategies

Search strategies for LF goals: depth-first (the default, as in the core), depth-bounded and
iterative deepening. A strategy applies to LF goals only; plain programs keep the fixed
depth-first order. The machine side is one integer per goal frame (the derivation depth) and
one flag per run (some goal was pruned by the bound).
-/

-- @lat: [[components#LF strategies]]

namespace Elpi.LF

/-- A search strategy for LF goals. -/
structure Strategy where
  name : String
  /-- Maximum derivation depth expanded in this run (`none` = unbounded). -/
  bound : Option Nat
  /-- Called when a run is exhausted; `cutoff` says whether the bound pruned anything.
  Returns the strategy of the next run, or `none` to stop. -/
  next? : (cutoff : Bool) → Option Strategy
  /-- Report an answer whose proof height is `h` only if `admits h` (iterative deepening
  uses a window so that answers are never repeated). -/
  admits : (h : Nat) → Bool

instance : Inhabited Strategy :=
  ⟨{ name := "dfs", bound := none, next? := fun _ => none, admits := fun _ => true }⟩

def dfs : Strategy :=
  { name := "dfs", bound := none, next? := fun _ => none, admits := fun _ => true }

def bounded (b : Nat) : Strategy :=
  { name := s!"bounded {b}", bound := some b, next? := fun _ => none, admits := fun _ => true }

/-- Iterative deepening: bounds 1, 2, 4, …; the answers of a run are those whose proof
height falls in the window `(prev, bound]`. -/
partial def iddfsFrom : Nat → Nat → Strategy
  | prev, b =>
    { name := "iddfs", bound := some b
      next? := fun cutoff => if cutoff then some (iddfsFrom b (2 * b)) else none
      admits := fun h => prev < h && h ≤ b }

def iddfs : Strategy := iddfsFrom 0 1

/-- Read the strategy selected by a directive. -/
-- @tg: implements:: [[openspec:elpi-lf#LF search strategies]]
def Strategy.ofDirective : String × Option Nat → Strategy
  | ("bounded", some n) => bounded n
  | ("iddfs", _) => iddfs
  | _ => dfs

end Elpi.LF
