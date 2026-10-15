import TestUtil
open Elpi TestUtil

/-! An `:index` specification only changes how many clauses are tried, never the answers. -/

-- @tg: verifies:: [[openspec:elpi-core-engine#Deep and multi-argument indexing#An index does not change the solutions]]
#eval show IO Unit from do
  let body := "pred p o:list int.\np [1, 2, 3].\np [1, 2, 4].\np [_, 2, 5].\np [7, 8, 9].\n"
  let plain ← sols (← load body) "p [1, 2, Z]"
  let indexed ← sols (← load (":index (3)\n" ++ body)) "p [1, 2, Z]"
  expectEq plain ["Z = 3", "Z = 4", "Z = 5"] "without the index"
  expectEq indexed plain "the index must not change the answers or their order"
  -- a deeper specification than the terms have, and one that stops short of the difference
  expectEq (← sols (← load (":index (9)\n" ++ body)) "p [1, 2, Z]") plain "depth beyond the terms"
  expectEq (← sols (← load (":index (2)\n" ++ body)) "p [1, 2, Z]") plain "depth short of the difference"

-- @tg: verifies:: [[openspec:elpi-core-engine#Deep and multi-argument indexing#Hypotheses are indexed like clauses]]
#eval show IO Unit from do
  let p ← load ":index (2)\npred q o:list int.\n"
  expectEq (← sols p "[q [1, 2], q [1, 3], q [_, 4], q [9, 9]] => q [1, X]") ["X = 2", "X = 3", "X = 4"]
    "hypotheses are filtered by the specification"
  -- a call whose argument is still a variable sees every hypothesis
  expectEq (← sols p "[q [1, 2], q [3, 4]] => q L") ["L = [1, 2]", "L = [3, 4]"] "unbound call argument"

-- @tg: verifies:: [[openspec:elpi-core-engine#Deep and multi-argument indexing#A later argument can be the only one indexed]]
#eval show IO Unit from do
  let p ← load ":index (_ 1)\npred r i:int, i:int.\nr A 1.\nr A 2.\nr A 3.\n"
  check ((← sols p "r 5 2").length == 1) "r 5 2 succeeds"
  check ((← sols p "r 5 4").isEmpty) "r 5 4 fails"
