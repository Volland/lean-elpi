import TestUtil
open Elpi TestUtil

/-- Load `main.elpi` from an in-memory file system. -/
def loadFiles (files : List (String × String)) : IO CompiledProgram := do
  let find (name from_ : String) : Id (Option (String × String)) :=
    (files.find? (·.1 == name)).map fun (n, t) => (n, t)
  let some (_, src) := files.find? (·.1 == "main") | fail "no main"
  match Id.run (loadUnits find "main.elpi" src) with
  | .error e => fail e.toString
  | .ok ds =>
    let base ← match baseProgram with | .ok b => pure b | .error e => fail s!"{e}"
    match base.addDecls ds with
    | .ok p => pure p
    | .error e => fail s!"{e}"

-- @tg: verifies:: [[openspec:elpi-core-engine#Accumulate and namespaces#Accumulated file is loaded once]]
#eval show IO Unit from do
  let p ← loadFiles
    [ ("main", "accumulate a.\naccumulate lib.")
    , ("a", "accumulate lib.")
    , ("lib", "pred l o:int.\nl 1.") ]
  expectEq (← sols p "l X") ["X = 1"] "l X (a single copy of lib)"

-- @tg: verifies:: [[openspec:elpi-core-engine#Accumulate and namespaces#Namespace qualifies predicate names]]
#eval show IO Unit from do
  let p ← load "namespace foo {\npred bar o:int.\nbar 1.\npred baz o:int.\nbaz X :- bar X.\n}"
  expectEq (← sols p "foo.baz X") ["X = 1"] "foo.baz X"
  match ← queryError p "bar X" with
  | some (.type m) => check (hasSub m "bar") s!"the error must name 'bar': {m}"
  | some e => fail s!"expected a type error, got {e}"
  | none => fail "bar X outside the namespace must be rejected"
