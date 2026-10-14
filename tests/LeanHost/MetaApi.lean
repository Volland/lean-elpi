import TestUtil
import Lean
open Elpi.Cmd Lean Meta

elpi_program metaprog
elpi_accumulate metaprog lp%{
  accumulate lean.
  pred nat o:int.
  nat 0.
  nat N :- nat M, N is M + 1.
}%

-- @tg: verifies:: [[openspec:lean-integration#Programmatic meta API#Elpi.query is usable from MetaM]]
#eval show MetaM Unit from do
  let s ← Elpi.query metaprog "lean.infer {{Nat.zero}} T"
  match s.head? with
  | some (.ok sol) =>
    match (sol.get? "T" : Option Expr) with
    | some e => unless e == mkConst ``Nat do throwError "unexpected type {e}"
    | none => throwError "T is not a term"
  | _ => throwError "no solution"
  -- taking only the first solutions of an infinite query terminates
  let nats ← Elpi.query metaprog "nat X"
  let firsts := nats.take 3
  unless firsts.length == 3 do throwError "expected three solutions"
