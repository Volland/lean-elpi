import TestUtil
import Lean
open Elpi TestUtil

-- @tg: verifies:: [[openspec:lean-integration#Source accumulation#Inline source error maps to the Lean position]]
#eval show IO Unit from do
  let src := "import Elpi\nopen Elpi.Cmd\nelpi_program myprog\nelpi_accumulate myprog lp%{ pred p i:int.\n  p X :- undeclared X. }%\n"
  let msgs ← elabSource src
  let errs := msgs.filter fun (sev, _, _, _) => sev == .error
  match errs with
  | [(_, line, col, text)] =>
    check (hasSub text "undeclared") s!"{text}"
    -- `undeclared` is on line 5 of the file, at column 9
    expectEq (line, col) (5, 9) "position of the offending token"
  | _ => fail s!"expected exactly one error, got {msgs}"

-- @tg: verifies:: [[openspec:lean-integration#Source accumulation#File accumulation]]
#eval show IO Unit from do
  withTmp fun dir => do
    IO.FS.writeFile (dir / "rules.elpi") "kind t type.\ntype a, b t.\npred edge i:t, o:t.\nedge a b.\n"
    let src := "import Elpi\nopen Elpi.Cmd\nelpi_program myprog\nelpi_accumulate myprog file \"" ++ (dir / "rules.elpi").toString ++ "\"\n#elpi myprog lp%{ edge a X }%\n"
    let msgs ← elabSource src
    check (msgs.any fun (sev, _, _, t) => sev == .information && t == "X = b") s!"{msgs}"
    -- a syntax error is reported as file:line:col
    IO.FS.writeFile (dir / "bad.elpi") "kind t type.\ntype a t.\np a :- .\n"
    let src := "import Elpi\nopen Elpi.Cmd\nelpi_program myprog\nelpi_accumulate myprog file \"" ++ (dir / "bad.elpi").toString ++ "\"\n"
    let msgs ← elabSource src
    check (msgs.any fun (sev, _, _, t) => sev == .error && hasSub t "bad.elpi:3:") s!"{msgs}"

-- position mapping with tabs, CRLF line ends and non-ASCII characters
def firstError (src : String) : IO (Nat × Nat × String) := do
  let msgs ← elabSource src
  match msgs.filter fun (sev, _, _, _) => sev == .error with
  | (_, l, c, t) :: _ => pure (l, c, t)
  | [] => fail s!"no error in {msgs}"

#eval show IO Unit from do
  let head := "import Elpi\nopen Elpi.Cmd\nelpi_program q\nelpi_accumulate q lp%{ pred p i:int.\n"
  -- a tab counts as one column
  let (l, c, _) ← firstError (head ++ "\tp X :- undeclared X. }%\n")
  expectEq (l, c) (5, 8) "tab"
  -- CRLF line endings: the lines of the file are those of the text
  let crlf := (head ++ "  p X :- undeclared X. }%\n").replace "\n" "\r\n"
  let (l, c, _) ← firstError crlf
  expectEq (l, c) (5, 9) "CRLF"
  -- non-ASCII characters before the token count as one column each
  let head2 := "import Elpi\nopen Elpi.Cmd\nelpi_program q\nelpi_accumulate q lp%{ pred p i:string, i:int.\n"
  let (l, c, _) ← firstError (head2 ++ "  p \"héllo\" X :- undeclared X. }%\n")
  expectEq (l, c) (5, 17) "non-ASCII"
