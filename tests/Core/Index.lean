import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#First-argument indexing#Clauses with a non-matching first argument are skipped]]
#eval show IO Unit from do
  let p ← load "p a 1.\np b 2.\np c 3."
  match p.prepare "p b X" with
  | .error e => fail s!"{e}"
  | .ok prep =>
    match Id.run (runLoop (p.env Id) prep.machine) with
    | .yield sol M =>
      expectEq (toString (mkSolution prep.syms prep.names sol)) "X = 2" "the answer"
      expectEq M.choices.size 0 "no choice point remains after the answer"
      -- a further solution fails immediately, without spending any fuel
      match Id.run (runLoop (p.env Id) M) with
      | .exhausted => pure ()
      | _ => fail "expected exhaustion"
    | _ => fail "expected a first solution"
