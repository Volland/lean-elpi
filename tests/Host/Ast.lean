import TestUtil
open Elpi TestUtil

private def astOf (src : String) : IO Host.Ast.Program :=
  match Host.ast [("org-rules", src)] with
  | .ok a => pure a
  | .error e => fail s!"program failed to load: {e}"

def orgDecls : String := "kind person type.
pred person.name o:person, o:string.
pred reports_to o:person, o:person, o:person.
pred check i:person.
check _.
"

-- @tg: verifies:: [[openspec:elpi-host-api#Public clause AST#Negation and cut are visible]]
#eval show IO Unit from do
  let a ← astOf (orgDecls ++ "pred v o:person.\nv P :- person.name P _, !, not (reports_to P _ _).")
  let some c := a.clauses.find? (·.pred == "v") | fail "the clause of v"
  match c.body with
  | .conj [.call "person.name" _, .cut, .not (.call "reports_to" _)] => pure ()
  | b => fail s!"unexpected body {repr b}"
  expectEq c.pos.line 7 "the clause keeps its line"
  check (a.preds.any (·.name == "reports_to")) "declarations are visible"

-- @tg: verifies:: [[openspec:elpi-host-api#Public clause AST#Hypothetical clause is visible]]
#eval show IO Unit from do
  let a ← astOf (orgDecls ++ "pred w i:person.\nw X :- (reports_to X E Y :- true) => check X.")
  let some c := a.clauses.find? (·.pred == "w") | fail "the clause of w"
  match c.body with
  | .impl [h] (.call "check" _) => expectEq h.pred? (some "reports_to") "the hypothetical clause's head"
  | b => fail s!"unexpected body {repr b}"
  -- builtins are told apart from calls, and accumulate directives are listed
  let b ← astOf "accumulate leq.\npred big i:int.\nbig N :- N > 10, std.length [N] 1."
  expectEq b.accumulates.toList ["leq"] "accumulate directives"
  match (b.clauses.find? (·.pred == "big")).map Host.Ast.Clause.body with
  | some (Host.Ast.Goal.conj [.builtin ">" _, .call "std.length" _]) => pure ()
  | b => fail s!"unexpected body {repr b}"
