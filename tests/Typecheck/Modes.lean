import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-typechecker#Mode declarations#Input argument is matched not unified]]
#eval show IO Unit from do
  let p ← load "pred p i:int, o:int.\np 1 2."
  expectEq (← sols p "p X Y") [] "p X Y with X unassigned must fail"
  expectEq (← sols p "p 1 Y") ["Y = 2"] "p 1 Y"
