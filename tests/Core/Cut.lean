import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Cut#Cut prunes remaining clauses of the predicate]]
#eval show IO Unit from do
  let p ← load "pred p o:int.\np 1 :- !.\np 2."
  expectEq (← sols p "p X") ["X = 1"] "p X"

-- @tg: verifies:: [[openspec:elpi-core-engine#Cut#Cut inside a called predicate does not escape it]]
#eval show IO Unit from do
  let p ← load "pred p o:int.\np 1 :- !.\np 2.\npred q o:int.\nq X :- p X.\nq 3."
  expectEq (← sols p "q X") ["X = 1", "X = 3"] "q X"
