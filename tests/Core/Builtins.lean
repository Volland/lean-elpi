import TestUtil
open Elpi TestUtil

abbrev OutM := StateM (Array String)
instance : Output OutM := ⟨fun s => modify (·.push s)⟩

-- @tg: verifies:: [[openspec:elpi-core-engine#Core builtins#Arithmetic evaluation with is]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "X is 2 + 3 * 4") ["X = 14"] "X"
  expectEq (← sols p "Y is 7 div 2") ["Y = 3"] "Y"
  expectEq (← sols p "Z is 7 mod 3") ["Z = 1"] "Z"
  for r in (solve p "W is 2.0 * 1.5").take 2 do
    match r with
    | .ok s =>
      match s.bindings.lookup "W" with
      | some (.lit (.float f)) => check (f == 3.0) s!"W = {f}"
      | _ => fail "W must be the float 3.0"
    | .error e => fail s!"{e}"
  match ← queryError p "V is U + 1" with
  | some (.runtime _) => pure ()
  | _ => fail "an unassigned operand must raise a runtime error"

-- @tg: verifies:: [[openspec:elpi-core-engine#Core builtins#Printing and string builtins]]
#eval show IO Unit from do
  let p ← load ""
  let (r, out) := (runIn (m := OutM) p "print \"a\" 1" : OutM _).run #[]
  match r with
  | .ok [_] => expectEq out #["a 1\n"] "print output"
  | _ => fail "print must succeed once"
  expectEq (← sols p "S is \"foo\" ^ \"bar\"") ["S = \"foobar\""] "string concatenation"
  -- `size` is an evaluable function in ELPI 1.18 (`N is size "hello"`), not a predicate
  expectEq (← sols p "N is size \"hello\"") ["N = 5"] "size"
