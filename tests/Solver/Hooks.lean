import TestUtil
import Solver.HookFixtures
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-solver-api#Unification hooks#Hook is consulted only when unification is stuck]]
#eval show IO Unit from do
  let p ← load ""
  let p := p.withHook countingHook
  hookCalls.set 0
  match (solve p "X = f a, F a = g a").toList with
  | [.ok s] =>
    expectEq (← hookCalls.get) 1 "the hook is called exactly once"
    expectEq s.constraints.length 1 "the stuck problem is a residual constraint"
  | _ => fail "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-solver-api#Unification hooks#Hook cannot override syntactic success]]
#eval show IO Unit from do
  let p ← load ""
  let p := p.withHook failingHook
  hookCalls.set 0
  expectEq (← sols p "f X = f a") ["X = a"] "f X = f a"
  expectEq (← hookCalls.get) 0 "the hook is never called"
