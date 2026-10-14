import TestUtil
open Elpi TestUtil

/-- A pure (non-`IO`) use of the library. -/
def pureAnswers (p : CompiledProgram) : List String :=
  (solve p "append [1] [2] L").toList.filterMap fun
    | .ok s => some (toString s)
    | .error _ => none

-- @tg: verifies:: [[openspec:elpi-runtime-library#Pure lazy queries#Query is a pure function]]
#eval show IO Unit from do
  let p ← load "pred append o:list A, o:list A, o:list A.\nappend [] L L.\nappend [X|XS] L [X|R] :- append XS L R."
  expectEq (pureAnswers p) ["L = [1, 2]"] "first evaluation"
  expectEq (pureAnswers p) ["L = [1, 2]"] "second evaluation"

-- @tg: verifies:: [[openspec:elpi-runtime-library#Pure lazy queries#Only demanded solutions are computed]]
#eval show IO Unit from do
  let p ← load "kind nat type.\ntype z nat.\ntype s nat -> nat.\npred nat o:nat.\nnat z.\nnat (s N) :- nat N."
  expectEq (← sols p "nat X" 3) ["X = z", "X = s z", "X = s (s z)"] "first three"
