import TestUtil
import Lean
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-core-engine#Monad-generic engine#Core runs without MetaM]]
#eval show IO Unit from do
  -- pure instance
  let p ← load "pred append o:list A, o:list A, o:list A.\nappend [] L L.\nappend [X|XS] L [X|R] :- append XS L R."
  expectEq (← sols p "append [1] [2] L") ["L = [1, 2]"] "append in the pure instance"
  -- the import closure of the core modules contains no Lean.Meta / Lean.Elab module
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elpi.Core.Machine }, { module := `Elpi.Core.Parser },
    { module := `Elpi.Core.Typecheck }, { module := `Elpi.Core.Builtins }] {}
  for m in env.header.moduleNames do
    let s := m.toString
    check (!(s.startsWith "Lean.Meta" || s.startsWith "Lean.Elab")) s!"core imports {s}"
