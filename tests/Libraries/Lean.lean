import TestUtil
import Lean
open Elpi TestUtil

-- @tg: verifies:: [[openspec:elpi-libraries#Lean API library#lean library declares the term type]]
#eval show IO Unit from do
  let prog := "pred head-const i:term, o:name.\nhead-const (app (const N _) _) N."
  -- with the library the program loads
  let _ ← load ("accumulate lean.\n" ++ prog)
  -- without it the types and constructors are undeclared
  let e ← loadErr prog
  check (hasSub e "term") s!"{e}"

-- the signatures of the lean.* builtins in lean.elpi are exactly those implemented in Lean
#eval show IO Unit from do
  let ref ← IO.mkRef ""
  let impl := (Host.leanBuiltins { phase := .query, lastError := ref }).map (·.sig.name)
  let some (_, src) := Std.embedded.find? (·.1 == "lean") | fail "no lean library"
  let declared := (src.splitOn "\n").filterMap fun l =>
    if l.startsWith "pred lean." then
      some ((l.drop 5).takeWhile (fun c => c != ' ')).toString
    else none
  -- lean.mk_app and lean.subst are written in ELPI, the rest are builtins
  let ours := declared.filter fun n => n != "lean.mk_app" && n != "lean.subst"
  for n in impl do
    check (ours.contains n) s!"builtin {n} has no signature in lean.elpi"
  for n in ours do
    check (impl.contains n) s!"lean.elpi declares {n}, which no builtin implements"
