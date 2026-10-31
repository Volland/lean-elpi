import TestUtil
open Elpi TestUtil

/-!
Guards against the engine copying its store or a term: each case is quadratic or worse if a
binding, a failed attempt or a hypothesis lookup costs time proportional to the size of what it
touches. The time bounds are generous; the failures they catch are minutes, not milliseconds.
-/

private def elapsedMs {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Binding a variable does not copy the term it is bound to]]
#eval show IO Unit from do
  let p ← load "type append list int -> list int -> list int -> prop.
append [X|XS] L [X|L1] :- append XS L L1.
append [] L L."
  -- ten elements doubled thirteen times: two lists of 81920 elements in the last append
  let base := "X0 = [1,2,3,4,5,6,7,8,9,10]"
  let steps := (List.range 13).map fun i => s!"append X{i} X{i} X{i+1}"
  let q := ", ".intercalate (base :: steps)
  let (sol, ms) ← elapsedMs (sols p q 1)
  check (sol.length == 1) "the append chain must succeed"
  check (ms < 30000) s!"appending long lists took {ms} ms: bindings are copying the list"

-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Backtracking in a large store]]
#eval show IO Unit from do
  let p ← load "type make int -> prop.
make 0.
make N :- N > 0, M is N - 1, sigma X\\ make M.
type pick int -> list int -> prop.
pick X [X|_].
pick X [_|T] :- pick X T."
  let items := ",".intercalate ((List.range 2000).map fun i => toString (i + 1))
  -- 100000 variables exist when the 2000 alternatives are tried; each starts clean
  let q := s!"make 100000, pick Y [{items}], Z = Y, Y = 2000"
  let (sol, ms) ← elapsedMs (sols p q 5)
  expectEq sol ["Y = 2000, Z = 2000"] "the only solution"
  check (ms < 30000) s!"backtracking over a large store took {ms} ms"

-- @tg: verifies:: [[openspec:elpi-core-engine#Hypothesis indexing#A goal picks the hypothesis about its own name]]
#eval show IO Unit from do
  let p ← load "kind nm type.
type p nm -> int -> prop.
type go int -> prop.
go 0.
go N :- N > 0, M is N - 1, pi x\\ p x N => (go M, p x N).
type two prop.
two :- pi x\\ pi y\\ (p x 1 => p y 1)."
  let (sol, ms) ← elapsedMs (sols p "go 300" 2)
  check (sol.length == 1) "every level finds its own hypothesis"
  check (ms < 30000) s!"300 nested hypotheses took {ms} ms"
  -- a hypothesis about one name never answers a goal about another
  expectEq (← sols p "two") [] "different eigenvariables are different"

/-- All solutions of a host query run in slices of `n` steps (the count, to force the run). -/
private partial def countSliced (q : Host.Query) (n : Nat) (acc : Nat := 0) : Nat :=
  match Host.runSlice q n with
  | .solution _ _ q' => countSliced q' n (acc + 1)
  | .paused q' => countSliced q' n acc
  | .exhausted | .error _ => acc

-- @tg: verifies:: [[openspec:elpi-host-api#Resumable fuel slices#Pausing does not copy the store]]
#eval show IO Unit from do
  -- a store that grows to 300000 variables: a copy per pause would cost far more than 10%
  let p ← match Host.loadUnits [("scaling", "pred make i:int.
make 0.
make N :- N > 0, M is N - 1, sigma X\\ make M.
pred run o:int.
run 1 :- make 300000.")] with
    | .ok p => pure p
    | .error e => fail s!"{e}"
  -- the best of three runs each, so a scheduling hiccup does not decide the comparison
  let mut single := 1000000
  let mut sliced := 1000000
  for _ in [0:3] do
    let some q := (Host.buildGoal p "run" #[.out "R"]).toOption | fail "goal"
    let (n1, t1) ← elapsedMs (IO.lazyPure fun _ => countSliced q defaultFuel)
    let some q' := (Host.buildGoal p "run" #[.out "R"]).toOption | fail "goal"
    let (n2, t2) ← elapsedMs (IO.lazyPure fun _ => countSliced q' 1000)
    check (n1 == 1 && n2 == 1) "one solution both ways"
    single := min single t1
    sliced := min sliced t2
  -- within 10%, plus 20 ms for the clock's granularity on short runs
  IO.println s!"pausing: one run {single} ms, slices of 1000 {sliced} ms"
  check (sliced * 10 ≤ single * 11 + 200) s!"slices of 1000 took {sliced} ms, one run {single} ms"
