import TestUtil
open Elpi Elpi.LF TestUtil

private def plusSrc (bad : Bool) : String :=
  "#lf\nnat : type.\nz : nat.\ns : nat -> nat.\nplus : nat -> nat -> nat -> type.\n#mode plus +N +M -P.\n" ++
  "plus_z : plus z M M.\nplus_s : plus (s N) M (s P) <- plus N M P.\n" ++
  (if bad then "plus_bad : plus (s N) M P <- plus N K P.\n" else "")

-- @tg: verifies:: [[openspec:elpi-lf#Mode checking#Mode-incorrect clause is reported]]
#eval show IO Unit from do
  let sig ← match loadSource "P" "p.elpi" (plusSrc true) with
    | .ok s => pure s | .error e => fail s!"{e}"
  let errs := checkModes sig
  check (errs.size == 1) s!"expected one mode error: {errs.map (·.toString)}"
  let m := errs[0]!.toString
  check (hasSub m "plus_bad" && hasSub m "plus N K P" && hasSub m "input argument 2" && hasSub m "`K`") m
  let ok ← match loadSource "P" "p.elpi" (plusSrc false) with
    | .ok s => pure s | .error e => fail s!"{e}"
  check (checkModes ok).isEmpty "plus_z and plus_s are mode-correct"
