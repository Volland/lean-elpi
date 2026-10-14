import TestUtil
open Elpi TestUtil

/-- Output sink for tests: `print` appends to the state. -/
abbrev OutM := StateM (Array String)
instance : Output OutM := ⟨fun s => modify (·.push s)⟩

-- @tg: verifies:: [[openspec:elpi-core-engine#Spilling#Spilled call is solved before the enclosing goal]]
#eval show IO Unit from do
  let p ← load "pred succ i:int, o:int.\nsucc X Y :- Y is X + 1."
  let (r, out) := (runIn (m := OutM) p "print {succ 1}" : OutM _).run #[]
  match r with
  | .ok [_] => expectEq out #["2\n"] "printed output"
  | .ok l => fail s!"expected one solution, got {l.length}"
  | .error e => fail s!"{e}"
