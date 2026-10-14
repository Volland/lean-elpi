import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#std list predicates behave like upstream]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "std.append [1] [2] L") ["L = [1, 2]"] "std.append"
  expectEq (← sols p "std.rev [1, 2, 3] R") ["R = [3, 2, 1]"] "std.rev"
  -- the oracle declares the first two arguments of std.append as inputs, so an unbound
  -- first argument has no solutions; the all-splits variant is std.appendR
  expectEq (← sols p "std.append X Y [1, 2]") [] "std.append with unbound inputs (as the oracle)"
  expectEq (← sols p "std.appendR X Y [1, 2]")
    ["X = [], Y = [1, 2]", "X = [1], Y = [2]", "X = [1, 2], Y = []"] "std.appendR splits"
  expectEq (← sols p "std.length [a, b, c] N") ["N = 3"] "std.length"
  expectEq (← sols p "std.nth 1 [a, b, c] X") ["X = b"] "std.nth"
  expectEq (← sols p "std.split-at 1 [1, 2, 3] A B") ["A = [1], B = [2, 3]"] "std.split-at"
  expectEq (← sols p "std.zip [1, 2] [a, b] Z") ["Z = [pr 1 a, pr 2 b]"] "std.zip"
  expectEq (← sols p "std.unzip [pr 1 a, pr 2 b] A B") ["A = [1, 2], B = [a, b]"] "std.unzip"
  expectEq (← sols p "std.flatten [[1], [2, 3]] F") ["F = [1, 2, 3]"] "std.flatten"
  expectEq (← sols p "std.last [1, 2, 3] X") ["X = 3"] "std.last"
  expectEq (← sols p "std.filter [1, 2, 3, 4] (x\\ x > 2) L") ["L = [3, 4]"] "std.filter"
  expectEq (← sols p "std.fold [1, 2, 3] 0 (x\\ a\\ r\\ r is a + x) S") ["S = 6"] "std.fold"
  expectEq (← sols p "std.exists [1, 2] (x\\ x > 1), std.forall [1, 2] (x\\ x > 0)") [""] "exists/forall"
  expectEq (← sols p "std.mem [1, 2] X") ["X = 1", "X = 2"] "std.mem"
  expectEq (← sols p "std.do! [X = 1, Y = 2]") ["X = 1, Y = 2"] "std.do!"

-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#std map operations]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "std.map.make cmp_term _M0, std.map.add 1 \"a\" _M0 _M1, std.map.add 2 \"b\" _M1 _M2, std.map.find 1 _M2 V, std.map.bindings _M2 B")
    ["V = \"a\", B = [pr 1 \"a\", pr 2 \"b\"]"] "map operations"
  expectEq (← sols p "std.map.make cmp_term _M0, std.map.add 1 \"a\" _M0 _M1, std.map.find 3 _M1 W") [] "missing key"
  expectEq (← sols p "std.map.make cmp_term _M0, std.map.add 1 \"a\" _M0 _M1, std.map.add 2 \"b\" _M1 _M2, std.map.remove 1 _M2 _M3, std.map.bindings _M3 B")
    ["B = [pr 2 \"b\"]"] "map remove"
  expectEq (← sols p "std.map [1, 2] (x\\ y\\ y is x * 2) L") ["L = [2, 4]"] "list map"
  expectEq (← sols p "std.set.make cmp_term _S0, std.set.add 3 _S0 _S1, std.set.add 1 _S1 _S2, std.set.elements _S2 E, std.set.mem 3 _S2")
    ["E = [1, 3]"] "set operations"
