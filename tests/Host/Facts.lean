import TestUtil
open Elpi TestUtil

private def hostLoad (src : String) : IO CompiledProgram :=
  match Host.loadUnits [("test", src)] with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

private def elapsedMs {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0)

def personDecls : String := "kind person type.\ntype person int -> person.\npred person.name o:person, o:string."

private def nameRows (n : Nat) : Array (Array Host.ResultTerm) :=
  (Array.range n).map fun k => #[.app "person" #[.int (Int.ofNat k)], .str s!"n{k}"]

-- @tg: verifies:: [[openspec:elpi-host-api#Bulk fact loading#Facts from terms answer queries]]
#eval show IO Unit from do
  let p ← hostLoad personDecls
  let p' ← match Host.addFacts p "person.name" (nameRows 100000) with
    | .ok p' => pure p'
    | .error e => fail s!"loading failed: {e}"
  match Host.buildGoal p' "person.name" #[.value (.app "person" #[.int 77]), .out "N"] with
  | .error e => fail s!"goal failed to build: {e}"
  | .ok q =>
    match Host.solveSliced q 1000 with
    | .ok sols => check (sols == #[#[("N", .str "n77")]]) s!"exactly one solution, N = \"n77\" ({sols.size} found)"
    | .error e => fail s!"query raised {e}"
  -- the original program is untouched, and first-argument indexing selects one clause
  expectEq (← sols p "person.name X Y") [] "the original program has no facts"
  expectEq (← sols p' "person.name (person 99999) Y") ["Y = \"n99999\""] "the last fact"

-- @tg: verifies:: [[openspec:elpi-host-api#Bulk fact loading#Loading is linear]]
#eval show IO Unit from do
  let p ← hostLoad personDecls
  let small := nameRows 100000
  let large := nameRows 1000000
  let (r1, t1) ← elapsedMs (IO.lazyPure fun _ => Host.addFacts p "person.name" small |>.toOption.map (·.items.size))
  let (r2, t2) ← elapsedMs (IO.lazyPure fun _ => Host.addFacts p "person.name" large |>.toOption.map (·.items.size))
  check (r1.isSome && r2.isSome) "both batches load"
  IO.println s!"facts: 10⁵ in {t1} ms, 10⁶ in {t2} ms"
  check (t2 ≤ 15 * max t1 10) s!"10⁶ facts took {t2} ms, 10⁵ took {t1} ms: more than 15 times"

-- @tg: verifies:: [[openspec:elpi-host-api#Bulk fact loading#Ill-typed fact is rejected]]
#eval show IO Unit from do
  let p ← hostLoad personDecls
  let rows := nameRows 10 |>.push #[.str "x", .int 1]
  match Host.addFacts p "person.name" rows with
  | .error (.fact "person.name" 11 1 _) => pure ()
  | .error e => fail s!"expected an error naming row 11, argument 1, got {e}"
  | .ok _ => fail "an ill-typed fact must reject the batch"
  -- nothing of the batch is added: the program is the one passed in
  expectEq (← sols p "person.name X Y") [] "no fact of the rejected batch"
