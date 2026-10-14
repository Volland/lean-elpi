import TestUtil
import Lean
open Elpi TestUtil

inductive Node | a | b | c deriving Elpi

-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed rule DSL#Ill-typed rule is rejected at compile time]]
#eval show IO Unit from do
  let src := "import Elpi\ninductive Node | a | b | c deriving Elpi\nelpi_rules graph where\n  pred edge : Node → Node → Prop\n  edge a \"b\".\n"
  let msgs ← elabSource src
  match msgs.filter fun (s, _, _, _) => s == .error with
  | [(_, line, col, text)] =>
    check (hasSub text "node") s!"expected type node missing: {text}"
    check (hasSub text "string") s!"actual type string missing: {text}"
    expectEq (line, col) (5, 9) "position of the offending token"
  | _ => fail s!"expected exactly one error, got {msgs}"

elpi_rules graph where
  pred edge : Node → Node → Prop
  pred path : Node → Node → Prop
  edge a b.
  edge b c.
  path X Y :- edge X Y.
  path X Y :- edge X Z, path Z Y.

-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed rule DSL#Rules compile to a program constant]]
#eval show IO Unit from do
  let before ← parserCalls.get
  let rs := (solveQuery (α := Node) graph.compiled (graph.path (.val Node.a) .out)).toList
  let nodes ← rs.mapM fun
    | .ok n => pure n
    | .error e => fail s!"{e}"
  check (nodes.length == 2) s!"expected two solutions, got {nodes.length}"
  check (match nodes with | [Node.b, Node.c] => true | _ => false) "solutions in order: b then c"
  expectEq (← parserCalls.get) before "program parser calls at run time"
