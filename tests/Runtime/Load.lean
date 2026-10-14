import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-runtime-library#Runtime program loading#Syntax error is returned as a value]]
#eval show IO Unit from do
  match Program.load "p 1" with
  | .ok _ => fail "a missing period must be a syntax error"
  | .error (.parse m) => check (hasSub m "<string>:1:3") s!"position at the end of the input: {m}"
  | .error e => fail s!"expected a parse error, got {e}"
