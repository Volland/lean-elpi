import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-typechecker#Type abbreviations#Abbreviation expands during checking]]
#eval show IO Unit from do
  let p ← load "typeabbrev env (list (pair string int)).\npred lookup i:env, i:string, o:int.\nlookup [pr K V|_] K V.\nlookup [_|L] K V :- lookup L K V.\npred t o:int.\nt V :- lookup [pr \"x\" 1] \"x\" V."
  expectEq (← sols p "t V") ["V = 1"] "t V"
  let e ← loadErr "typeabbrev a (list a)."
  check (hasSub e "cyclic") s!"a cyclic abbreviation must be rejected: {e}"
