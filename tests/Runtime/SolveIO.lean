import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-runtime-library#IO queries#IO builtin is usable from solveIO]]
#eval show IO Unit from do
  let p ← load ""
  let (out, r) ← IO.FS.withIsolatedStreams (do
    let st ← solveIO p "print \"hello\", X = 1"
    st.next)
  expectEq out "hello\n" "standard output"
  match r with
  | some s => expectEq (toString s) "X = 1" "first solution"
  | none => fail "no solution"
  -- an engine error is raised as an IO exception
  let q ← load "pred bad.\nbad :- X is Y + 1."
  let ok ← try
      let st ← solveIO q "bad"
      let _ ← st.next
      pure false
    catch _ => pure true
  check ok "the engine error must surface as an IO exception"
