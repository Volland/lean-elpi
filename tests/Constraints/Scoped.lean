import TestUtil
open Elpi TestUtil

abbrev OutM := StateM (Array String)
instance : Output OutM := ⟨fun s => modify (·.push s)⟩

def scopedProg : String := "pred mem i:int.\npred chk i:int, i:int.\nchk C _ :- mem C, print \"mem visible\"."

-- @tg: verifies:: [[openspec:elpi-constraints#Scoped constraints#Constraint under pi respects eigenvariables]]
#eval show IO Unit from do
  let p ← load scopedProg
  let (r, out) := (runIn (m := OutM) p "pi c\\ ((mem c => declare_constraint (chk c X) [X]), X = 1)" : OutM _).run #[]
  match r with
  | .ok [_] => expectEq out #["mem visible\n"] "chk c 1 resumes with mem c visible"
  | _ => fail "expected exactly one solution"
  expectEq (← sols p "pi c\\ (declare_constraint (chk c X) [X], X = c)") [] "X was created outside the scope of c"
  -- a rule head (Ctx ?- C) binds the recorded context
  let q ← load (scopedProg ++ "\nconstraint chk {\n  rule (G ?- chk C N) <=> (print G).\n}")
  let (r, out) := (runIn (m := OutM) q "pi c\\ (mem c => declare_constraint (chk c X) [X])" : OutM _).run #[]
  match r with
  | .ok _ => check (out.any (hasSub · "mem")) s!"the recorded context includes mem c: {out}"
  | .error e => fail s!"{e}"
