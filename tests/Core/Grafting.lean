import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Clause names and grafting#Clause grafted before a named clause]]
#eval show IO Unit from do
  let p ← load "pred r o:int.\n:name \"base\" r 1.\n:before \"base\" r 0."
  expectEq (← sols p "r X") ["X = 0", "X = 1"] "r X"

-- @tg: verifies:: [[openspec:elpi-core-engine#Clause names and grafting#Clause grafted after a named clause]]
#eval show IO Unit from do
  let p ← load "pred r o:int.\n:name \"base\" r 1.\nr 3.\n:after \"base\" r 2."
  expectEq (← sols p "r X") ["X = 1", "X = 2", "X = 3"] "r X"
  -- unknown and duplicate names are load-time errors
  let e1 ← loadErr "pred r o:int.\n:before \"nope\" r 0."
  check (hasSub e1 "nope") s!"unknown clause name must be reported: {e1}"
  let e2 ← loadErr "pred r o:int.\n:name \"a\" r 1.\n:name \"a\" r 2."
  check (hasSub e2 "duplicate") s!"duplicate clause name must be reported: {e2}"
