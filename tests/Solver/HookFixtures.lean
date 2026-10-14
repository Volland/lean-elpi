import Elpi

/-! Unification hook fixtures: a call-counting hook that suspends, and a hook that fails on
everything. The counters are observed by the tests. -/

open Elpi

initialize hookCalls : IO.Ref Nat ← IO.mkRef 0

@[noinline] unsafe def bumpHook (n : Nat) : Nat := unsafeBaseIO (do hookCalls.modify (· + 1); pure n)
@[implemented_by bumpHook] opaque noteHook (n : Nat) : Nat

def countingHook : UnifHook where
  onStuck _ _ _ d := if noteHook d > 100000000 then .fail else .suspend

def failingHook : UnifHook where
  onStuck _ _ _ d := if noteHook d > 100000000 then .suspend else .fail
