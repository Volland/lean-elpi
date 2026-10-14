import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-runtime-library#Runtime builtins#Builtin attached with withBuiltin is callable]]
#eval show IO Unit from do
  let p ← load ""
  match p.withFn1 "double" "pred double i:int, o:int." (fun (n : Int) => [2 * n]) with
  | .error e => fail s!"{e}"
  | .ok p' =>
    expectEq (← sols p' "double 21 X") ["X = 42"] "double 21 X"
    -- a name clash is an error
    match p'.withFn1 "double" "pred double i:int, o:int." (fun (n : Int) => [n]) with
    | .ok _ => fail "a duplicate builtin must be rejected"
    | .error _ => pure ()
