import TestUtil
import Lean
open Elpi TestUtil

-- @tg: verifies:: [[openspec:lean-reflection#Typed marshalling classes#Nat round-trips through ToElpi and FromElpi]]
#eval show IO Unit from do
  match (fromElpi (toElpi (42 : Nat)) : Except DecodeError Nat) with
  | .ok n => expectEq n 42 "Nat"
  | .error e => fail s!"{e}"
  match (fromElpi (toElpi [(1, "a"), (2, "b")]) : Except DecodeError (List (Nat × String))) with
  | .ok l => expectEq l [(1, "a"), (2, "b")] "List (Nat × String)"
  | .error e => fail s!"{e}"
  match (fromElpi (toElpi (some #[true, false])) : Except DecodeError (Option (Array Bool))) with
  | .ok l => expectEq l (some #[true, false]) "Option (Array Bool)"
  | .error e => fail s!"{e}"
  match (fromElpi (toElpi (Lean.Name.mkStr `Foo "bar")) : Except DecodeError Lean.Name) with
  | .ok n => expectEq n (Lean.Name.mkStr `Foo "bar") "Name"
  | .error e => fail s!"{e}"
  -- numbers outside the ELPI int range fail to encode instead of wrapping
  match encodeNat (2 ^ 70) with
  | .error m => check (hasSub m "range") m
  | .ok _ => fail "overflow must be an error"

-- @tg: verifies:: [[openspec:lean-reflection#Typed marshalling classes#Decoding a wrong shape fails]]
#eval show IO Unit from do
  match (fromElpi (toElpi "x") : Except DecodeError Nat) with
  | .error e =>
    expectEq e.expected "int" "expected type"
    check (hasSub e.got "x") s!"the offending term must be shown: {e.got}"
  | .ok _ => fail "decoding a string as a Nat must fail"
