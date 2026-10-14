import TestUtil
import Solver.HandlerFixtures
import Lean
open Elpi TestUtil Lean

def liaProg (env : Environment) : IO CompiledProgram :=
  match Registry.loadIn env "" (extraSigs := ["pred lia.le o:int, o:int."]) with
  | .ok p => pure p
  | .error e => fail s!"{e}"

-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler simplifies a new constraint]]
#eval show CoreM Unit from do
  let p ← liaProg (← getEnv)
  match (solve p "declare_constraint (lia.le X 3) [X], declare_constraint (lia.le X 5) [X]").toList with
  | [.ok s] =>
    expectEq s.constraintLines.length 1 "a single residual constraint"
    check (hasSub s.constraintLines.head! "lia.le X0 3") s!"{s.constraintLines}"
  | _ => throwError "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler wakes on variable instantiation]]
#eval show CoreM Unit from do
  let p ← liaProg (← getEnv)
  expectEq (← sols p "declare_constraint (lia.le X 3) [X], X = 7") [] "onWake fails for X = 7"
  match (solve p "declare_constraint (lia.le X 3) [X], X = 2").toList with
  | [.ok s] => expectEq s.constraints.length 0 "no residual constraint after X = 2"
  | _ => throwError "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler state backtracks with the store]]
#eval show CoreM Unit from do
  let p ← liaProg (← getEnv)
  match (solve p "(declare_constraint (lia.le X 3) [X], fail ; declare_constraint (lia.le X 5) [X])").toList with
  | [.ok s] =>
    expectEq s.constraintLines.length 1 "a single residual constraint"
    check (hasSub s.constraintLines.head! "lia.le X0 5") s!"{s.constraintLines}"
  | _ => throwError "expected exactly one solution"
