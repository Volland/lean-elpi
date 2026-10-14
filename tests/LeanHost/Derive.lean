import TestUtil
import Lean
open Elpi TestUtil Lean

inductive Color | red | green deriving Elpi

structure Point where
  x : Nat
  y : Nat
  deriving Elpi

-- @tg: verifies:: [[openspec:lean-reflection#Deriving Elpi#Inductive emits kind and type declarations]]
#eval show CoreM Unit from do
  let env ← getEnv
  let ds := derivedSignatures env
  check (ds.contains "kind color type.") s!"{ds}"
  check (ds.contains "type red color.") s!"{ds}"
  check (ds.contains "type green color.") s!"{ds}"
  -- red is the ELPI constant `red`
  match toElpi Color.red with
  | .const c => expectEq (Symbols.initial.intern "red").1.idx c.idx "constant id of red"
  | _ => throwError "expected a constant"

-- @tg: verifies:: [[openspec:lean-reflection#Deriving Elpi#Structure emits a constructor declaration]]
#eval show CoreM Unit from do
  let ds := derivedSignatures (← getEnv)
  check (ds.contains "kind point type.") s!"{ds}"
  check (ds.contains "type point.mk int -> int -> point.") s!"{ds}"
  let sym := (Symbols.initial.intern "point.mk").1
  match (fromElpi (Elpi.Term.app (.const sym) #[.lit (.int 1), .lit (.int 2)]) : Except DecodeError Point) with
  | .ok p => expectEq (p.x, p.y) (1, 2) "decoded point"
  | .error e => throwError "{e}"
