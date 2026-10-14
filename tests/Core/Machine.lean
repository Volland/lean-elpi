import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Deep recursion does not overflow the native stack]]
#eval show IO Unit from do
  let p ← load "pred count i:int.\ncount 0.\ncount N :- N > 0, M is N - 1, count M."
  expectEq (← sols p "count 1000000") [""] "count 1000000"

-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Fuel exhaustion reports a resource error]]
#eval show IO Unit from do
  let p ← load "pred loop.\nloop :- loop."
  match ← queryError p "loop" 10000 with
  | some .outOfFuel => pure ()
  | some e => fail s!"expected the out-of-fuel error, got {e}"
  | none => fail "the run must not end with failure or success"
  -- distinguishable from an ordinary failure
  let q ← load "pred nope.\nnope :- fail."
  expectEq (← queryError q "nope" 10000).isNone true "failure is not an error"

-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Solutions are produced lazily]]
#eval show IO Unit from do
  let p ← load "kind nat type.\ntype z nat.\ntype s nat -> nat.\npred nat o:nat.\nnat z.\nnat (s N) :- nat N."
  expectEq (← sols p "nat X" 3) ["X = z", "X = s z", "X = s (s z)"] "first three solutions"
