import TestUtil
open Elpi TestUtil

def leqDef : String := "pred leq o:int, o:int.\nleq A B :- declare_constraint (leq A B) [A, B]."

-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Simplification rule replaces constraints]]
#eval show IO Unit from do
  let p ← load ("constraint leq {\n  rule \\ (leq X Y) (leq Y X) <=> (X = Y).\n}\n" ++ leqDef)
  match (solve p "leq P Q, leq Q P").toList with
  | [.ok s] =>
    expectEq s.constraints.length 0 "both leq constraints are removed"
    match s.bindings.lookup "P", s.bindings.lookup "Q" with
    | some (.uvar a _), some (.uvar b _) => check (a == b) "P and Q must be unified"
    | _, _ => fail "P and Q must be unassigned variables"
  | _ => fail "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Propagation rule adds constraints]]
#eval show IO Unit from do
  let p ← load ("constraint leq {\n  rule (leq X Y) \\ (leq X Y).\n  rule (leq X Y) (leq Y Z) <=> (leq X Z).\n}\n" ++ leqDef)
  match (solve p "leq A B, leq B C").toList with
  | [.ok s] =>
    expectEq s.constraints.length 3 "leq A B, leq B C and leq A C"
    let lines := s.constraintLines
    check (lines.any (hasSub · "leq X0 X1")) s!"{lines}"
    check (lines.any (hasSub · "leq X2 X1")) s!"{lines}"
    check (lines.any (hasSub · "leq X0 X2")) s!"{lines}"
  | _ => fail "expected exactly one solution"

-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Failing guard prevents firing]]
#eval show IO Unit from do
  let pos := "pred pos o:int, o:int.\npos X N :- declare_constraint (pos X N) [X]."
  let p ← load ("constraint pos {\n  rule \\ (pos X N) | (N > 0) <=> true.\n}\n" ++ pos)
  match (solve p "pos X 0").toList with
  | [.ok s] => expectEq s.constraints.length 1 "pos X 0 stays: its guard fails"
  | _ => fail "expected exactly one solution"
  match (solve p "pos X 1").toList with
  | [.ok s] => expectEq s.constraints.length 0 "pos X 1 is removed"
  | _ => fail "expected exactly one solution"
  -- a guard may not assign the frozen variable X
  let q ← load ("constraint pos {\n  rule \\ (pos X N) | (X = 1) <=> true.\n}\n" ++ pos)
  match (solve q "pos X 0").toList with
  | [.ok s] => expectEq s.constraints.length 1 "the rule must not fire"
  | _ => fail "expected exactly one solution"

-- freezing: matching a rule head never assigns a variable of the store
#eval show IO Unit from do
  let p ← load ("constraint leq {\n  rule \\ (leq X Y) (leq Y X) <=> (X = Y).\n}\n" ++ leqDef)
  match p.prepare "leq P Q" with
  | .error e => fail s!"{e}"
  | .ok prep =>
    match Id.run (runLoop (p.env Id prep.syms) prep.machine) with
    | .yield sol _ =>
      let s := sol.store
      let before := s.nextVar
      -- match the active constraint against every position of the rule
      let blocks := p.blocks
      for c in s.cstore.toList do
        for b in blocks do
          for r in b.rules do
            for pos in [0:2] do
              for mt in matchRule (some cTurn) r s c pos do
                for i in [0:before] do
                  check (!(mt.store.isAssigned ⟨i⟩) || s.isAssigned ⟨i⟩) "a stored variable was assigned"
    | _ => fail "expected a solution"
