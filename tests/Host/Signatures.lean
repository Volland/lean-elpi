import TestUtil
open Elpi TestUtil

def hostLoad (src : String) : IO CompiledProgram :=
  match Host.loadUnits [("test", src)] with
  | .ok p => pure p
  | .error e => fail s!"program failed to load: {e}"

-- @tg: verifies:: [[openspec:elpi-host-api#Predicate signature lookup#Declared predicate]]
#eval show IO Unit from do
  let p ← hostLoad "kind dept type.\nkind person type.\npred violation i:dept, o:person, o:string."
  let some s := Host.predSig? p "violation" | fail "violation must be declared"
  expectEq (s.args.map (·.ty)).toList [.const "dept", .const "person", .const "string"] "argument types"
  check (s.args.map (·.mode) == #[.i, .o, .o]) "modes i, o, o"
  -- arguments declared with `type` default to mode o
  let q ← hostLoad "kind person type.\ntype knows person -> person -> prop."
  let some k := Host.predSig? q "knows" | fail "knows must be a predicate"
  check (k.args.map (·.mode) == #[.o, .o]) "type-declared arguments have mode o"

-- @tg: verifies:: [[openspec:elpi-host-api#Predicate signature lookup#Polymorphic predicate]]
#eval show IO Unit from do
  let p ← hostLoad "pred closure i:(A -> A -> prop), i:A, o:A."
  let some s := Host.predSig? p "closure" | fail "closure must be declared"
  expectEq s.args[0]!.ty (.arrow (.var "A") (.arrow (.var "A") (.const "prop"))) "first argument"
  expectEq s.args[1]!.ty (.var "A") "second argument stays a variable"

-- @tg: verifies:: [[openspec:elpi-host-api#Predicate signature lookup#Unknown predicate]]
#eval show IO Unit from do
  let p ← hostLoad "kind person type.\ntype alice person."
  check (Host.predSig? p "nothing_here").isNone "an undeclared name has no signature"
  check (Host.predSig? p "alice").isNone "a constructor is not a predicate"
