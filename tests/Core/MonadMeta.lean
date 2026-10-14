import TestUtil
import Lean
open Elpi TestUtil Lean Meta

def assignM : Builtin MetaM :=
  { sig := { name := "assign-m", modes := #[], type := .con "any" [] }
    run := fun c args => do
      -- create a metavariable and assign it
      let m ← mkFreshExprMVar (mkConst ``Nat)
      m.mvarId!.assign (mkNatLit 0)
      return .alts c.store (.cons args (Thunk.mk fun _ => .nil)) }


def checkUnassigned : Builtin MetaM :=
  { sig := { name := "check-m-unassigned", modes := #[], type := .con "any" [] }
    run := fun c args => do
      -- no metavariable assigned in the failed branch may be left assigned
      let mctx ← getMCtx
      let any := mctx.eAssignment.toList.any fun _ => true
      if any then return .fail
      return .alts c.store (.cons args (Thunk.mk fun _ => .nil)) }

-- @tg: verifies:: [[openspec:elpi-core-engine#Monad-generic engine#MetaM instance rewinds metavariable assignments]]
#eval show MetaM Unit from do
  let p ← match Program.load "pred assign-m.\npred check-m-unassigned." with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let r ← runIn (m := MetaM) p "(assign-m, fail) ; check-m-unassigned" [assignM, checkUnassigned]
  match r with
  | .ok [_] => pure ()
  | .ok l => throwError "expected one solution, got {l.length}"
  | .error e => throwError "{e}"
