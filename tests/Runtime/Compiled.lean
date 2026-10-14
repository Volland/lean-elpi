import TestUtil
import Lean
open Elpi TestUtil

elpi_program fam "parent tom bob."

-- @tg: verifies:: [[openspec:elpi-runtime-library#Compiled program constants#Program constant needs no parsing at runtime]]
#eval show IO Unit from do
  let before ← parserCalls.get
  expectEq (← sols fam.compiled "parent tom X") ["X = bob"] "parent tom X"
  expectEq (← parserCalls.get) before "program parser calls during the run"
