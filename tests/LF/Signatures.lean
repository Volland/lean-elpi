import TestUtil
open Elpi Elpi.LF TestUtil

private def stlcSrc : IO String := IO.FS.readFile "tests/LF/stlc.elpi"

private def lines (s : String) : Nat := (s.splitOn "\n").length - 1

private def answersOf (sig : LFSig) (q : String) : IO (List String) := do
  let prog ← match elaborate sig with | .ok p => pure p | .error e => fail e
  let mut out := []
  for r in (runQuery sig prog q).take 5 do
    match r with
    | .ok a => out := out ++ [a.showBindings]
    | .error e => fail s!"{e}"
  return out

-- @tg: verifies:: [[openspec:elpi-lf#LF opt-in per file#lf header enables dependent checking]]
#eval show IO Unit from do
  let src ← stlcSrc
  -- with `bad`: an LF type error at the first `base` argument of `app`
  match loadSource "stlc" "stlc.elpi" (src ++ "bad : of (app base base) base.\n") with
  | .ok _ => fail "bad should be rejected"
  | .error e =>
    check (e.decl == "bad") s!"declaration: {e.decl}"
    expectEq (e.pos.line, e.pos.col) (lines src + 1, 14) "position of the first base"
    check (hasSub e.msg "expected type tm but found tp") e.msg
  -- without it: the signature loads and answers the query
  match loadSource "stlc" "stlc.elpi" src with
  | .error e => fail s!"{e}"
  | .ok sig => expectEq (← answersOf sig "of (lam base x\\ x) T") ["T = arr base base"] "answers"

-- @tg: verifies:: [[openspec:elpi-lf#LF opt-in per file#Plain file is unaffected]]
#eval show IO Unit from do
  let plain := "kind tm type.\ntype base tm.\ntype app tm -> tm -> tm.\npred size i:tm, o:int.\n" ++
    "size base 1.\nsize (app A B) N :- size A NA, size B NB, N is NA + NB + 1.\n"
  let p ← load plain
  expectEq (← sols p "size (app base (app base base)) N") ["N = 5"] "plain answers"
  -- LF directives and LF declarations are parse errors outside `#lf` files
  let e ← loadErr "#strategy iddfs.\n"
  check (hasSub e "1:") s!"directive error should carry a position: {e}"
  let e2 ← loadErr "c : tm.\n"
  check (hasSub e2 "1:") s!"declaration error should carry a position: {e2}"
  -- a file without the header is never read as LF
  check (!LFSyntax.isLF "plain.elpi" plain) "plain file detected as LF"

-- @tg: verifies:: [[openspec:elpi-lf#Dependent signatures#Ill-typed LF object is rejected]]
#eval show IO Unit from do
  let src ← stlcSrc
  match loadSource "stlc" "stlc.elpi" (src ++ "bad2 : of (lam base base) base.\n") with
  | .ok _ => fail "bad2 should be rejected"
  | .error e =>
    check (e.decl == "bad2") s!"declaration: {e.decl}"
    check (e.pos.line == lines src + 1) s!"line: {e.pos.line}"
    check (hasSub e.msg "tm -> tm" && hasSub e.msg "tp") e.msg

-- @tg: verifies:: [[openspec:elpi-lf#Dependent signatures#Type family is indexed by objects]]
#eval show IO Unit from do
  let vec := "#lf\nnat : type.\nz : nat.\ns : nat -> nat.\nvec : nat -> type.\nvnil : vec z.\n" ++
    "vcons : nat -> vec N -> vec (s N).\n"
  match loadSource "v" "v.elpi" (vec ++ "wrong : vec (s z) <- vec z.\n") with
  | .error e => fail s!"{e}"
  | .ok sig =>
    let syms := sig.order.foldl (fun (sy : Symbols) n => (sy.intern n).2) Symbols.initial
    expectEq (showTy syms {} #[] (sig.consts["vcons"]!)) "pi N:nat\\ nat -> vec N -> vec (s N)" "type of vcons"
  match loadSource "v" "v.elpi" (vec ++ "tp : type.\nbase : tp.\nwrong2 : vec base.\n") with
  | .ok _ => fail "wrong2 should be rejected: base is not a nat"
  | .error e => check (hasSub e.msg "expected type nat but found tp") e.msg
