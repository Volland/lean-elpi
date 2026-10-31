import TestUtil
open Elpi TestUtil

private def hostLoad (src : String) : IO CompiledProgram :=
  match Host.loadUnits [("test", src)] with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

private def firstSolution (p : CompiledProgram) (pred : String) (args : Array Host.GoalArg) :
    IO (Array (String × Host.ResultTerm)) := do
  match Host.buildGoal p pred args with
  | .error e => fail s!"goal failed to build: {e}"
  | .ok q =>
    match Host.solveSliced q 1000 (limit := 1) with
    | .ok #[bs] => pure bs
    | .ok r => fail s!"expected one solution, got {r.size}"
    | .error e => fail s!"query raised {e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Structured solution terms#Constructor application]]
#eval show IO Unit from do
  let p ← hostLoad "kind person type.\ntype person int -> person.\npred boss o:person, o:list string, o:float.\nboss (person 42) [\"a\", \"b\"] 1.5."
  let bs ← firstSolution p "boss" #[.out "P", .out "L", .out "F"]
  check (bs[0]! == ("P", .app "person" #[.int 42])) s!"P = person 42, got {bs[0]!.2}"
  check (bs[1]! == ("L", .list #[.str "a", .str "b"])) s!"L is a list of two strings, got {bs[1]!.2}"
  check (bs[2]!.2.toFloat? == some 1.5) "F = 1.5"

-- @tg: verifies:: [[openspec:elpi-host-api#Structured solution terms#Unbound output]]
#eval show IO Unit from do
  let p ← hostLoad "kind person type.\npred anyone o:person.\nanyone _."
  let bs ← firstSolution p "anyone" #[.out "P"]
  check (bs == #[("P", .unbound)]) s!"P is the unbound marker, got {bs.map (·.2)}"

-- @tg: verifies:: [[openspec:elpi-host-api#Structured solution terms#JSON form round-trips]]
#eval show IO Unit from do
  -- `Host.ResultTerm.json_roundtrip` proves it for every term; this checks the compiled code
  let ts : List Host.ResultTerm :=
    [.app "person" #[.int 42, .list #[.str "a\"b", .ofFloat (-0.0), .ofFloat (1.0/0.0)]],
     .unbound, .lam, .opaque "handle" "7", .const "[]", .list #[]]
  for t in ts do
    check (Host.ResultTerm.fromJson? (Host.ResultTerm.toJson t) == some t) s!"{t} round-trips"
    let text := (Host.ResultTerm.toJson t).compress
    match Lean.Json.parse text with
    | .ok j => check (Host.ResultTerm.fromJson? j == some t) s!"{t} round-trips through text"
    | .error e => fail e
