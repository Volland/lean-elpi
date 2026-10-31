import TestUtil
open Elpi TestUtil

private def hostLoad (src : String) : IO CompiledProgram :=
  match Host.loadUnits [("test", src)] with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

private def goal (p : CompiledProgram) (pred : String) (args : Array Host.GoalArg) : IO Host.Query :=
  match Host.buildGoal p pred args with
  | .ok q => pure q
  | .error e => fail s!"goal failed to build: {e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Goals built from terms#Input values are not parsed as source]]
#eval show IO Unit from do
  let p ← hostLoad "kind person type.\ntype person int -> person.\npred name_of i:string, o:person.\nname_of S (person N) :- N is size S."
  let evil := "x\" , evil Y"
  let q ← goal p "name_of" #[.value (.str evil), .out "P"]
  -- the goal is one call with one string literal and one fresh variable, nothing else
  match q.machine.goals with
  | [f] =>
    match f.goal with
    | .app (.const _) #[.lit (.str s), .uvar _ _] => expectEq s evil "the string literal"
    | _ => fail "the goal must be name_of applied to a string literal and a variable"
  | gs => fail s!"expected one goal, found {gs.length}"
  expectEq (q.names.map (·.1)).toList ["P"] "the only query variable"
  match Host.solveSliced q 1000 with
  | .ok #[#[("P", .app "person" #[.int n])]] => expectEq n (Int.ofNat evil.length) "the string reached the engine unchanged"
  | .ok r => fail s!"unexpected solutions: {r.map (·.map (·.2.toString))}"
  | .error e => fail s!"query raised {e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Goals built from terms#Ill-typed argument]]
#eval show IO Unit from do
  let p ← hostLoad "kind person type.\ntype person int -> person.\npred manages i:person, o:person."
  match Host.buildGoal p "manages" #[.value (.int 3), .out "Q"] with
  | .error (.argument "manages" 1 _) => pure ()
  | .error e => fail s!"expected an error naming argument 1, got {e}"
  | .ok _ => fail "an integer where a person is declared must be rejected"
  -- a nested mismatch names the argument it sits in
  match Host.buildGoal p "manages" #[.value (.app "person" #[.str "x"]), .out "Q"] with
  | .error (.argument "manages" 1 _) => pure ()
  | .error e => fail s!"expected an error naming argument 1, got {e}"
  | .ok _ => fail "person \"x\" must be rejected"
  match Host.buildGoal p "nobody" #[] with
  | .error (.unknownPred "nobody") => pure ()
  | _ => fail "an undeclared predicate has no goal"
