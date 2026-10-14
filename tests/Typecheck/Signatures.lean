import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-typechecker#Signature declarations#Undeclared constant is reported]]
#eval show IO Unit from do
  let e ← loadErr "pred p i:int.\np foo."
  check (hasSub e "foo") s!"the error must name the undeclared constant foo: {e}"

-- @tg: verifies:: [[openspec:elpi-typechecker#Signature declarations#Kind and type declarations are accepted]]
#eval show IO Unit from do
  let p ← load "kind nat type.\ntype z nat.\ntype s nat -> nat.\npred even i:nat.\neven z.\neven (s (s N)) :- even N."
  expectEq (← sols p "even (s (s z))") [""] "even (s (s z))"
  expectEq (← sols p "even (s z)") [] "even (s z)"
