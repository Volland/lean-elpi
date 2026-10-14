import TestUtil
import Solver.RegistrationA
import Lean
open Elpi TestUtil Lean

def loadWith (env : Environment) (src : String) : IO CompiledProgram :=
  match Registry.loadIn env src with
  | .ok p => pure p
  | .error e => fail s!"{e}"

-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin signature is typechecked]]
#eval show CoreM Unit from do
  let env ← getEnv
  match Registry.loadIn env "q X :- succ \"a\" X." with
  | .ok _ => throwError "the ill-typed call must be rejected"
  | .error e =>
    unless hasSub (toString e) "a" do throwError "{e}"
  -- a malformed signature fails with a parse error
  match Registry.checkSig "succ" "pred succ i:int o:" with
  | .ok _ => throwError "the malformed signature must be rejected"
  | .error msg => unless hasSub msg "signature" do throwError "{msg}"

-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin returns a stream of solutions]]
#eval show CoreM Unit from do
  let env ← getEnv
  let p ← loadWith env ""
  expectEq (← sols p "between 1 3 X") ["X = 1", "X = 2", "X = 3"] "between 1 3 X"
  -- demanding one solution calls the implementation once
  betweenCalls.set 0
  let _ ← sols p "between 1 100 X" 1
  expectEq (← betweenCalls.get) 1 "implementation calls for one demanded solution"

-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin runs in the host monad]]
#eval show MetaM Unit from do
  let env ← getEnv
  let p ← match Registry.loadIn env "" with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let bs ← match Registry.metaBuiltins env with
    | .ok bs => pure bs
    | .error e => throwError "{e}"
  let before := (← getMCtx).decls.toList.length
  let r ← runIn (m := Meta.MetaM) p "(mk-mvar, fail) ; true" bs
  match r with
  | .ok [_] => pure ()
  | _ => throwError "the query must succeed once"
  unless (← getMCtx).decls.toList.length == before do
    throwError "the metavariable of the failed branch is still in the context"
