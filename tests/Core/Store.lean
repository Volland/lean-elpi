import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Backtracking restores the substitution]]
#eval show IO Unit from do
  let p ← load ""
  let mut n := 0
  for r in (solve p "(X = 1, Y = a, fail) ; Z = X").take 5 do
    match r with
    | .ok s =>
      n := n + 1
      match s.bindings.lookup "X", s.bindings.lookup "Y", s.bindings.lookup "Z" with
      | some (.uvar x #[]), some (.uvar y #[]), some (.uvar z #[]) =>
        -- X and Y are unassigned again; Z is bound to X
        check (z == x) "Z must be X"
        check (y != x) "Y must be a different variable"
      | _, _, _ => fail s!"bindings were not as expected: {s}"
    | .error e => fail s!"{e}"
  expectEq n 1 "number of solutions"

/-- A host monad with a counter, to observe choice points restoring host state. -/
abbrev CounterM := StateM Nat

def counterBuiltins : List (Builtin CounterM) :=
  [ { sig := { name := "incr", modes := #[], type := .con "any" [] }
      run := fun c args => do
        modify (· + 1)
        return .alts c.store (.cons args (Thunk.mk fun _ => .nil)) },
    { sig := { name := "read-counter", modes := #[.o], type := .con "any" [] }
      run := fun c _ => do
        let n ← get
        return .alts c.store (.cons #[.lit (.int n)] (Thunk.mk fun _ => .nil)) } ]

-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Choice point restores host monad state]]
#eval show IO Unit from do
  let p ← load "pred incr.\npred read-counter o:int."
  let (r, final) := (runIn (m := CounterM) p "(incr, fail) ; read-counter N" counterBuiltins : CounterM _).run 0
  match r with
  | .ok [s] =>
    expectEq (toString s) "N = 0" "the increment of the failed branch must be rolled back"
    expectEq final 0 "final counter"
  | .ok l => fail s!"expected one solution, got {l.length}"
  | .error e => fail s!"{e}"
