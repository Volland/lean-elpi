import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed query decoding#Solutions decode to a Lean type]]
#eval show IO Unit from do
  let p ← load "pred q o:int, o:list int.\nq 1 [2, 3]."
  match (solveAs (α := Nat × List Nat) p "q X Y").toList with
  | [.ok (a, b)] =>
    expectEq a 1 "first component"
    expectEq b [2, 3] "second component"
  | _ => fail "expected exactly one decoded value"

-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed query decoding#Decoding failure is reported]]
#eval show IO Unit from do
  let p ← load "pred r o:string.\nr \"one\"."
  match (solveAs (α := Nat) p "r X").toList with
  | [.error e] =>
    let m := toString e
    check (hasSub m "X") s!"the error must name the variable: {m}"
    check (hasSub m "Nat") s!"the error must name the expected type: {m}"
  | _ => fail "expected a decoding error"
