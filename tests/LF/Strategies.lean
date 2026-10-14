import TestUtil
open Elpi Elpi.LF TestUtil

private def src (strat : String) : String :=
  "#lf\no : type.\na : o.\np : o -> type.\np_loop : p X <- p X.\np_a : p a.\n#strategy " ++ strat ++ ".\n"

private def answers (strat q : String) (n : Nat) (fuel : Nat) : IO (List String) := do
  let sig ← match loadSource "S" "s.elpi" (src strat) with
    | .ok s => pure s | .error e => fail s!"{e.msg}"
  let prog ← match elaborate sig with | .ok p => pure p | .error e => fail e
  let mut out := []
  for r in (runQuery sig prog q fuel).take n do
    match r with
    | .ok a => out := out ++ [a.showProof]
    | .error e => out := out ++ [s!"error: {e}"]
  return out

-- @tg: verifies:: [[openspec:elpi-lf#LF search strategies#Iterative deepening finds a proof that depth-first misses]]
#eval show IO Unit from do
  let d ← answers "dfs" "p a" 1 100000
  check (d.length == 1 && (hasSub d.head! "error")) s!"dfs should exhaust fuel: {d}"
  let i ← answers "iddfs" "p a" 4 100000
  check (i.length == 4) s!"iddfs answers: {i}"
  expectEq i.head! "p_a" "first iddfs proof"
  check (i.tail.all (· != "p_a")) s!"p_a repeated: {i}"
  -- the later answers are the longer derivations, each reported exactly once
  let want := ["p_a", "p_loop a p_a", "p_loop a (p_loop a p_a)", "p_loop a (p_loop a (p_loop a p_a))"]
  check (want.all i.contains) s!"missing proofs: {i}"
  check (i.eraseDups.length == i.length) s!"a proof was reported twice: {i}"
