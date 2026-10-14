import TestUtil
import Lean
open Elpi.Cmd Lean Meta

elpi_program qprog
elpi_accumulate qprog lp%{
  accumulate lean.
  pred p o:term.
  p T :- T = {{ fun x : Nat => x + 1 }}.
}%

-- @tg: verifies:: [[openspec:lean-reflection#Quotations#Quotation elaborates to a term]]
#eval show MetaM Unit from do
  let s ← Elpi.query qprog "p T"
  let some (.ok sol) := s.head? | throwError "no solution"
  let some (e : Expr) := sol.get? "T" | throwError "T is not a reifiable term"
  let stx ← match Parser.runParserCategory (← getEnv) `term "fun x : Nat => x + 1" with
    | .ok s => pure s | .error m => throwError m
  let expected ← Elab.Term.TermElabM.run' (do
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e)
  unless e.equal expected do throwError "{e} is not {expected}"

-- @tg: verifies:: [[openspec:lean-reflection#Quotations#Antiquotation splices an ELPI variable]]
#eval show MetaM Unit from do
  let s ← Elpi.query qprog "X = {{ (2 : Nat) }}, T = {{ lp:{{X}} + 1 }}"
  let some (.ok sol) := s.head? | throwError "no solution"
  let some t := sol.find? "T" | throwError "T unbound"
  -- instance holes of the quotation stay metavariables until Lean unifies them
  let e ← match Elpi.Reflect.ofTerm (sol.store.zonk t 0) (fun _ => .error "var") with
    | .ok e => pure e
    | .error _ =>
      -- reify with metavariables for the remaining ELPI variables
      let vars := Elpi.Unify.collectUVars sol.store t 0
      let mut m : Std.HashMap Elpi.UVarId Expr := {}
      for u in vars do m := m.insert u (← mkFreshExprMVar none)
      match Elpi.Reflect.ofTerm (sol.store.zonk t 0) (fun u => match m[u]? with | some e => .ok e | none => .error "var") with
      | .ok e => pure e
      | .error msg => throwError "{msg}"
  let stx ← match Parser.runParserCategory (← getEnv) `term "(2 : Nat) + 1" with
    | .ok s => pure s | .error m => throwError m
  let expected ← Elab.Term.TermElabM.run' (do
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e)
  unless ← isDefEq e expected do throwError "{e} is not {expected}"
  unless (← instantiateMVars e).equal expected do throwError "{← instantiateMVars e} differs from {expected}"
