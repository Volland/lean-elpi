import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Depth-first search order#Answers follow clause order]]
#eval show IO Unit from do
  let p ← load "pred p o:int.\np 1.\np 2.\np 3.\npred q o:int.\nq X :- p X.\nq 0."
  expectEq (← sols p "q X") ["X = 1", "X = 2", "X = 3", "X = 0"] "q X"
