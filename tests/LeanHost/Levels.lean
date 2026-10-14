import TestUtil
import Lean
open Elpi TestUtil Lean

def lvl (l : Level) : Elpi.Term := Elpi.Term.app (.const cSortR) #[Reflect.levelTerm l]

-- @tg: verifies:: [[openspec:lean-reflection#Opaque universe levels#Levels compare by handle identity]]
#eval show IO Unit from do
  let u := Level.param `u
  let v := Level.param `v
  let s : Store := {}
  -- Sort u reflected twice unifies
  check (unify s (lvl u) (lvl u) 0).isSome "equal levels share a handle"
  -- Sort (max u v) and Sort (max v u) are different handles
  check (unify s (lvl (.max u v)) (lvl (.max v u)) 0).isNone "levels are compared by identity"
  -- the same two are equal for Lean, which `lean.defeq` decides (see LeanHost/Builtins)
  check (Level.isEquiv (.max u v) (.max v u)) "Lean normalises them to the same level"
