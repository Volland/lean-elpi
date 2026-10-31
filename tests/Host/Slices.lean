import TestUtil
open Elpi TestUtil

/-! Resumable fuel slices: a query run in slices of any size gives the same solutions, in the
same order, with the same ending (exhaustion or running out of the whole budget), as one run. -/

private def hostLoad (src : String) : IO CompiledProgram :=
  match Host.loadUnits [("test", src)] with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

/-- Every solution and how the search ended, running in slices of `n` steps. -/
private partial def runAll (q : Host.Query) (n : Nat) :
    Array (Array (String × Host.ResultTerm)) × String :=
  go q #[] 0
where
  go (q : Host.Query) (acc : Array (Array (String × Host.ResultTerm))) (pauses : Nat) :
      Array (Array (String × Host.ResultTerm)) × String :=
    match Host.runSlice q n with
    | .solution bs _ q' => go q' (acc.push bs) pauses
    | .paused q' => go q' acc (pauses + 1)
    | .exhausted => (acc, "exhausted")
    | .error e => (acc, s!"error: {e}")

def slicesProgram : String := "
pred between i:int, i:int, o:int.
between L H L :- L =< H.
between L H X :- L < H, L1 is L + 1, between L1 H X.
pred hit o:int.
hit X :- between 1 150000 X, 0 is X mod 5000.
pred grouped o:int, o:int.
grouped X N :- between 1 40 X, std.findall (between 1 X _) L, std.length L N."

private def goalOf (p : CompiledProgram) (pred : String) (args : Array Host.GoalArg)
    (fuel : Nat := defaultFuel) : IO Host.Query :=
  match Host.buildGoal p pred args fuel with
  | .ok q => pure q
  | .error e => fail s!"goal failed to build: {e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Resumable fuel slices#Slices equal one run]]
#eval show IO Unit from do
  let p ← hostLoad slicesProgram
  -- about 10⁶ steps; then a query whose findall crosses slice boundaries
  for (pred, args) in [("hit", #[Host.GoalArg.out "X"]), ("grouped", #[.out "X", .out "N"])] do
    let (want, wantEnd) := runAll (← goalOf p pred args) defaultFuel
    check (want.size > 0) s!"{pred} has solutions"
    expectEq wantEnd "exhausted" s!"{pred}: one run ends by exhaustion"
    for n in [1, 3, 17, 1000, 4096, 99991] do
      let (got, gotEnd) := runAll (← goalOf p pred args) n
      check (got == want) s!"{pred} in slices of {n}: same solutions in the same order"
      expectEq gotEnd wantEnd s!"{pred} in slices of {n}: same ending"
  -- a budget that runs out midway runs out at the same point however it is sliced
  for budget in [50000, 333333] do
    let (want, wantEnd) := runAll (← goalOf p "hit" #[.out "X"] budget) budget
    check (wantEnd.startsWith "error") s!"a budget of {budget} runs out"
    for n in [1, 999, 50000] do
      let (got, gotEnd) := runAll (← goalOf p "hit" #[.out "X"] budget) n
      check (got == want && gotEnd == wantEnd) s!"budget {budget} in slices of {n}: same solutions, then out of fuel"
