import TestUtil
import Lean
open Elpi.Cmd Lean Elab Command

elpi_program bprog
elpi_accumulate bprog lp%{ accumulate lean. }%

-- @tg: verifies:: [[openspec:lean-integration#Lean builtins#lean.infer returns the type]]
/-- info: T = {{Nat → Nat}} -/
#guard_msgs in
#elpi bprog lp%{ lean.infer {{Nat.succ}} T }%

-- @tg: verifies:: [[openspec:lean-integration#Lean builtins#lean.defeq decides definitional equality]]
/-- info: true -/
#guard_msgs in
#elpi bprog lp%{ lean.defeq {{2 + 2}} {{4}} }%

/-- error: query has no solution -/
#guard_msgs in
#elpi bprog lp%{ lean.defeq {{2}} {{3}} }%

/-- info: T = {{1 + 1}}, R = {{2}} -/
#guard_msgs in
#elpi bprog lp%{ lean.defeq {{Sort (max 1 2)}} {{Sort 2}}, lean.elab "1 + 1" {{Nat}} T, lean.whnf T R }%

-- the metavariable created in a failed branch is rolled back
#eval show CommandElabM Unit from do
  let t ← match Elpi.Parser.parseQuery "lp%" "(lean.mk_mvar {{Nat}} M, lean.defeq M {{1}}, fail ; true)" with
    | .ok t => pure t
    | .error e => throwError "{e.toString}"
  let t ← match ← liftTermElabM (Elpi.Quote.elabTm t) with
    | .ok t => pure t
    | .error (_, m) => throwError "{m}"
  let before ← liftTermElabM do pure (← getMCtx).decls.toList.length
  let r ← liftTermElabM (runQuery (← getEnv) `bprog t .query 1)
  match r with
  | .ok [_] => pure ()
  | _ => throwError "the query must succeed once"
  let after ← liftTermElabM do pure (← getMCtx).decls.toList.length
  unless before == after do throwError "the metavariable of the failed branch is still in the context"
