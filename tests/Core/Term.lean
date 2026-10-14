import TestUtil
open Elpi TestUtil

def lowerSrc (src : String) : IO Term := do
  match Parser.parseQuery "<t>" src with
  | .error e => fail e.toString
  | .ok t => pure ((lowerTm #[] t).run { syms := Symbols.initial }).1

-- @tg: verifies:: [[openspec:elpi-core-engine#Term representation#Bound variables use de Bruijn levels]]
#eval show IO Unit from do
  let t1 ← lowerSrc "x\\ y\\ x"
  let t2 ← lowerSrc "a\\ b\\ a"
  check (t1 == t2) "the two α-equivalent terms are not structurally equal"
  check (hash t1 == hash t2) "the two α-equivalent terms hash differently"
  check (t1 == .lam (.lam (.bound 0))) "the body does not refer to the outer binder by level 0"

-- @tg: verifies:: [[openspec:elpi-core-engine#Term representation#Unification variables carry their scope level]]
#eval show IO Unit from do
  let p ← load ""
  -- assigning `X := c` would let `X` (level 0) mention the eigenvariable `c` (level 1)
  expectEq (← sols p "pi c\\ X = c") [] "pi c\\ X = c"
  -- the level of a variable is recorded in the store
  let s : Store := {}
  let (u, s) := s.fresh 3
  let (v, s) := s.fresh 0
  expectEq (s.levelOf u) 3 "level of the first variable"
  expectEq (s.levelOf v) 0 "level of the second variable"
