import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Universal goal introduces a fresh constant]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "pi x\\ x = x") [""] "pi x\\ x = x"
  expectEq (← sols p "pi x\\ pi y\\ x = y") [] "pi x\\ pi y\\ x = y"

-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Implication extends the program locally]]
#eval show IO Unit from do
  let p ← load "pred q o:int."
  expectEq (← sols p "q 1 => q X") ["X = 1"] "q 1 => q X"
  expectEq (← sols p "q Y") [] "the hypothetical clause must be gone"

-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Disjunction backtracks into the second branch]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "(X = 1 ; X = 2), X > 1") ["X = 2"] "disjunction"
