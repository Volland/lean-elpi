import TestUtil
open Elpi Elpi.LF TestUtil

private def stlc : IO String := IO.FS.readFile "tests/LF/stlc.elpi"

private def setup (extra : String := "") : IO (LFSig × CompiledProgram) := do
  match loadSource "stlc" "stlc.elpi" ((← stlc) ++ extra) with
  | .error e => fail s!"{e}"
  | .ok sig =>
    match elaborate sig with
    | .ok p => pure (sig, p)
    | .error e => fail e

-- @tg: verifies:: [[openspec:elpi-lf#Pattern unification for LF#LF unification stays in the pattern fragment]]
#eval show IO Unit from do
  let (sig, prog) ← setup
  -- `E x = app x x` is a pattern problem: the query fails finitely, with nothing suspended
  let rs := (runQuery sig prog "of (lam base (y\\ app y y)) T").take 5
  expectEq rs.length 0 "no answers"
  -- outside the pattern fragment the problem is suspended and reported with the answer
  let (sig2, prog2) ← setup "c : tm.\np : tm -> type.\np_c : p c.\nq : (tm -> tm) -> type.\nq_c : q F <- p (F (app c c)).\n"
  match (runQuery sig2 prog2 "q G").take 1 with
  | [.ok a] => check (!a.constraints.isEmpty) "the answer must carry the residual problem"
  | _ => fail "q G should have one answer"

-- @tg: verifies:: [[openspec:elpi-lf#Proof term recording#Successful query yields a derivation term]]
#eval show IO Unit from do
  let (sig, prog) ← setup
  match (runQuery sig prog "of (lam base x\\ x) T").take 1 with
  | [.ok a] =>
    expectEq a.showBindings "T = arr base base" "bindings"
    expectEq a.showProof "of_lam base (x0\\ x0) base (x0\\ x1\\ x1)" "proof term"
    -- the LF re-check accepts the proof at the instantiated query
    let .atom fam args := a.ty | fail "not a judgment"
    let args := args.map fun t => a.store.zonk t 0
    match certificate sig a.syms fam args a.proof (recheck := true) with
    | .ok _ => pure ()
    | .error e => fail s!"re-check failed: {e.msg}"
  | _ => fail "expected one answer"
