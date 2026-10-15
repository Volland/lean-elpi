import TestUtil
open Elpi TestUtil

/-!
Clause selection without per-call work: candidate arrays prepared by the index, compiled clause
bodies, hypotheses indexed by predicate and key, and term instantiation that keeps sharing.
-/

private def elapsedMs {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

-- @tg: verifies:: [[openspec:elpi-core-engine#First-argument indexing#Variable-headed clauses keep their place among keyed ones]]
#eval show IO Unit from do
  let p ← load "type p string -> int -> prop.\np \"a\" 1.\np X 2.\np \"b\" 3.\np \"a\" 4."
  expectEq (← sols p "p \"a\" N") ["N = 1", "N = 2", "N = 4"] "bucket of a merged with the variable clause"
  expectEq (← sols p "p \"c\" N") ["N = 2"] "a key without a bucket gets the variable clauses"
  expectEq (← sols p "p K 3") ["K = \"b\""] "a variable first argument tries every clause"

-- @tg: verifies:: [[openspec:elpi-core-engine#Hypothesis indexing#Hypotheses about other predicates are not consulted]]
#eval show IO Unit from do
  let p ← load "type q int -> prop.
type count int -> prop.
count 0.
count N :- N > 0, M is N - 1, count M.
type mk int -> prop -> prop.
mk 0 G :- G.
mk N G :- N > 0, M is N - 1, q N => mk M G."
  let (bare, t0) ← elapsedMs (sols p "count 50000" 1)
  let (hyp, t1) ← elapsedMs (sols p "mk 2000 (count 50000)" 1)
  check (bare.length == 1 && hyp.length == 1) "both runs succeed"
  -- scanning 2000 hypotheses on each of the 50000 calls would make the second run many times slower
  check (t1 < 3 * t0 + 500) s!"count took {t0} ms alone and {t1} ms under 2000 hypotheses about q"

-- @tg: verifies:: [[openspec:elpi-core-engine#Compiled clauses and term sharing#Cut in a compiled body]]
#eval show IO Unit from do
  let p ← load "type p int -> prop.\np 1.\np 2.\ntype r int -> prop.\nr X :- p X, !, X > 0.\nr 3."
  expectEq (← sols p "r X") ["X = 1"] "the cut in the middle of the body prunes p and r"
  let q ← load "type s int -> prop.\ns X :- true, X = 1, true.\ns 2."
  expectEq (← sols q "s X") ["X = 1", "X = 2"] "true goals are dropped, the rest kept in order"

-- @tg: verifies:: [[openspec:elpi-core-engine#Compiled clauses and term sharing#Instantiating a clause body keeps its ground parts]]
#eval show IO Unit from do
  let ground : Term := .app (.const ⟨2000000⟩) #[.lit (.int 1), .app (.const ⟨2000001⟩) #[.lit (.str "x")]]
  let body : Term := .app (.const ⟨2000002⟩) #[.cvar 0 #[], ground]
  match Term.renameCVars #[.lit (.int 7)] 0 body with
  | .app _ #[v, g] =>
    expectEq (v == .lit (.int 7)) true "the clause variable is replaced"
    check (Term.sameRef g ground) "the ground argument is the same object, not a copy"
  | t => fail s!"unexpected shape {repr t}"
  check (Term.sameRef (Term.renameCVars #[] 0 ground) ground) "a ground body is returned as it is"
  check (Term.sameRef (({} : Store).zonk ground 0) ground) "zonk keeps a term without variables"
