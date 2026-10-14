import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-typechecker#Prenex polymorphism#Polymorphic predicate is used at two types]]
#eval show IO Unit from do
  let p ← load "pred len i:list A, o:int.\nlen [] 0.\nlen [_|T] N :- len T M, N is M + 1.\npred both o:int, o:int.\nboth N M :- len [1, 2] N, len [\"a\"] M."
  expectEq (← sols p "both N M") ["N = 2, M = 1"] "both N M"
