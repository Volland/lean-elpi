import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-runtime-library#Persistent program extension#Asserting a clause leaves the original program unchanged]]
#eval show IO Unit from do
  let p ← load "pred q o:int.\nq 1."
  match p.assert "q 2." with
  | .error e => fail s!"{e}"
  | .ok p' =>
    expectEq (← sols p "q X") ["X = 1"] "original program"
    expectEq (← sols p' "q X") ["X = 1", "X = 2"] "extended program"
