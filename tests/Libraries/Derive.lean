import TestUtil
import Lean
open Elpi TestUtil

inductive Color | red | green

inductive Shape | dot | circle (r : Nat) | rect (w h : Nat)

-- @tg: verifies:: [[openspec:elpi-libraries#Derive library#Derived BEq instance is accepted by Lean]]
elpi_derive BEq Color

example : (Color.red == Color.red, Color.red == Color.green) = (true, false) := rfl

elpi_derive BEq Shape
elpi_derive Repr Shape
elpi_derive Repr Color
elpi_derive DecidableEq Color

example : (Shape.rect 1 2 == Shape.rect 1 2, Shape.rect 1 2 == Shape.rect 1 3, Shape.dot == Shape.circle 0)
    = (true, false, false) := by decide

example : (if Color.red = Color.green then 1 else 2) = 2 := by decide

/-- info: "Shape.circle 3" -/
#guard_msgs in
#eval toString (repr (Shape.circle 3))

-- unsupported classes and shapes are reported by name
#eval show IO Unit from do
  let msgs ← elabSource "import Elpi\ninductive T | a\nelpi_derive Ord T\n"
  check (msgs.any fun (s, _, _, t) => s == .error && hasSub t "Ord") s!"{msgs}"
  let msgs ← elabSource "import Elpi\ninductive Q (α : Type) | a (x : α)\nelpi_derive BEq Q\n"
  check (msgs.any fun (s, _, _, t) => s == .error && hasSub t "parameters") s!"{msgs}"
