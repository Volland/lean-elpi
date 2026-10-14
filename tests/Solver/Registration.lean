import TestUtil
import Solver.RegistrationA
import Lean
open Elpi TestUtil Lean

-- @tg: verifies:: [[openspec:elpi-solver-api#Attribute registration#Solver from an imported module is available]]
#eval show CoreM Unit from do
  let env ← getEnv
  let names := (Registry.entries env).toList.map (·.name)
  unless names.contains "double" do throwError "double is not registered: {names}"
  let p ← match Registry.loadIn env "" with
    | .ok p => pure p
    | .error e => throwError "{e}"
  expectEq (← sols p "double 21 X") ["X = 42"] "double 21 X"
