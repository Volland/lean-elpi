import TestUtil
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-typechecker#Load-time type errors with positions#Ill-typed clause is rejected at load time]]
#eval show IO Unit from do
  let e ← loadErr "pred p i:int.\np \"x\"."
  check (hasSub e "string") s!"the error must state the inferred type string: {e}"
  check (hasSub e "int") s!"the error must state the expected type int: {e}"
  -- no program value is produced
  match Program.load "pred p i:int.\np \"x\"." with
  | .ok _ => fail "a program was produced"
  | .error _ => pure ()

-- @tg: verifies:: [[openspec:elpi-typechecker#Load-time type errors with positions#Error reports the source position]]
#eval show IO Unit from do
  match Program.load "pred p i:int.\n\np \"x\".\n" (file := "bad.elpi") with
  | .ok _ => fail "expected a type error"
  | .error e =>
    let m := toString e
    check (hasSub m "bad.elpi:3:2") s!"position of the term \"x\" expected (bad.elpi:3:2): {m}"

-- constraint handling belongs to a later milestone and is rejected at load time
#eval show IO Unit from do
  let e ← loadErr "pred p.\np :- declare_constraint (p) []."
  check (hasSub e "unsupported") s!"declare_constraint must be rejected: {e}"
  let e ← loadErr "constraint foo { }."
  check (hasSub e "unsupported") s!"constraint blocks must be rejected: {e}"
