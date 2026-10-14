import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Pattern problem has a most general unifier]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "pi a\\ pi b\\ X a b = f b a") ["X = c0 \\ c1 \\ f c1 c0"]
    "pattern problem solutions"

-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Occurs check rejects cyclic solution]]
#eval show IO Unit from do
  let p ← load ""
  expectEq (← sols p "X = f X") [] "X = f X"
  expectEq (← sols p "X = f Y, Y = g X") [] "X = f Y, Y = g X"

-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Problem outside the pattern fragment is suspended]]
#eval show IO Unit from do
  let p ← load ""
  -- the suspended conjunct is re-checked once X is assigned by the second conjunct
  expectEq (← sols p "pi a\\ (X a a = f a, X = x\\ y\\ f y)") ["X = c0 \\ c1 \\ f c1"]
    "suspended problem is re-checked"
  -- alone, it succeeds with a residual delayed goal and no assignment of X
  let mut n := 0
  for r in (solve p "pi a\\ X a a = f a").take 5 do
    match r with
    | .ok s =>
      n := n + 1
      expectEq s.constraints.length 1 "residual delayed goals"
      match s.bindings.lookup "X" with
      | some (.uvar _ _) => pure ()
      | _ => fail "X must stay unassigned"
    | .error e => fail s!"unexpected error {e}"
  expectEq n 1 "number of solutions"

/-- A list of `n` integers as a term. -/
def intList (n : Nat) : Term :=
  (List.range n).foldr (fun i acc => Term.app (.const cCons) #[.lit (.int (Int.ofNat i)), acc])
    (.const cNil)

-- unifying two 10^6-element lists does not overflow the native stack (explicit worklist)
#eval show IO Unit from do
  let n := 1000000
  let (u, s) := ({} : Store).fresh 0
  let t1 := Term.app (.const cCons) #[.uvar u #[], intList n]
  let t2 := Term.app (.const cCons) #[.lit (.int 7), intList n]
  match unify s t1 t2 0 with
  | some s' =>
    expectEq (s'.deref (.uvar u #[]) 0 == .lit (.int 7)) true "the head variable is bound"
  | none => fail "unification of two long lists failed"
