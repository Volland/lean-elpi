import TestUtil
open Elpi TestUtil

abbrev OutM := StateM (Array String)
instance : Output OutM := ⟨fun s => modify (·.push s)⟩

def evenProg : String := "pred even i:int.\neven N :- 0 is N mod 2, print \"even\" N."

-- @tg: verifies:: [[openspec:elpi-constraints#Delayed goals#Goal suspends on an unassigned variable]]
#eval show IO Unit from do
  let p ← load evenProg
  let (r, out) := (runIn (m := OutM) p "declare_constraint (even X) [X], print \"after\"" : OutM _).run #[]
  match r with
  | .ok [s] =>
    expectEq out #["after\n"] "no clause of even runs"
    expectEq s.constraints.length 1 "one suspended goal"
    expectEq (s.constraintLines.length) 1 "one residual line"
    check (hasSub (s.constraintLines.head!) "even X0  /* suspended on X0 */") s!"{s.constraintLines}"
  | _ => fail "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-constraints#Delayed goals#Suspended goal resumes on assignment]]
#eval show IO Unit from do
  let p ← load evenProg
  let (r, out) := (runIn (m := OutM) p "declare_constraint (even X) [X], X = 4, print \"done\"" : OutM _).run #[]
  match r with
  | .ok [s] =>
    -- `even 4` runs right after `X = 4`, before `print "done"`
    expectEq out #["even 4\n", "done\n"] "resumption order"
    expectEq s.constraints.length 0 "no suspended goal remains"
    expectEq (toString s) "X = 4" "answer"
  | _ => fail "expected exactly one solution"
  expectEq (← sols p "declare_constraint (even X) [X], X = 3") [] "the resumed goal even 3 fails"
