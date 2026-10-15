import TestUtil
open Elpi TestUtil

/-!
ELPI 1.18 syntax and library features that the upstream programs use: macros, multi-name
binders, blanks before a backslash, a trailing comma in a list, `:index` before a declaration,
warnings for undeclared constants in untyped programs, and the balanced `std.map` / `std.set`.
-/

-- @tg: verifies:: [[openspec:elpi-core-engine#ELPI 1.18 surface syntax#A macro with and without parameters]]
#eval show IO Unit from do
  let p ← load "macro @n :- 3.\nmacro @twice X :- (X + X).\nmain :- Y is @twice @n, Y = 6."
  check ((← sols p "main").length == 1) "macros must expand: @twice @n is 3 + 3"

-- @tg: verifies:: [[openspec:elpi-core-engine#ELPI 1.18 surface syntax#Several names in one binder]]
#eval show IO Unit from do
  let p ← load ""
  check ((← sols p "(pi x y\\ x = x), (sigma A B\\ A = 1, B = 2, A = 1)").length == 1)
    "pi x y\\ and sigma A B\\ bind several names"

-- @tg: verifies:: [[openspec:elpi-core-engine#ELPI 1.18 surface syntax#A binder with blanks and a list with a trailing comma]]
#eval show IO Unit from do
  let p ← load ""
  match ← sols p "F = (x \\ y \\ x), [1, 2, ] = L, R = F 1 2" with
  | [s] =>
    check (hasSub s "R = 1") s!"the binder with blanks applies: {s}"
    check (hasSub s "L = [1, 2]") s!"the trailing comma is accepted: {s}"
  | l => fail s!"expected one solution, got {l}"

-- @tg: verifies:: [[openspec:elpi-core-engine#ELPI 1.18 surface syntax#An index attribute before a declaration]]
#eval show IO Unit from do
  let p ← load ":index (1)\npred p i:int.\np 1."
  check ((← sols p "p 1").length == 1) "an index attribute may precede a declaration"
  check ((← sols p "p 2").isEmpty) "and does not change what the predicate means"

-- @tg: verifies:: [[openspec:elpi-typechecker#Signature declarations#Undeclared constant in an untyped program is a warning]]
#eval show IO Unit from do
  let p ← load "main :- X = (1 :: nil), print X."
  check (p.warnings.any (hasSub · "nil")) s!"a warning must name nil: {p.warnings}"
  check ((← sols p "main").length == 1) "the program still runs"
  -- a program with declarations keeps the error
  let e ← loadErr "pred p i:int.\np foo."
  check (hasSub e "foo") s!"an undeclared constant of a typed program is an error: {e}"

-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#Maps and sets stay ordered through removal]]
#eval show IO Unit from do
  let p ← load ""
  let q := "std.int.set.empty E, std.fold {std.rev {std.iota 200}} E std.int.set.add S, " ++
    "std.filter {std.int.set.elements S} (x\\ not (0 is x mod 3)) Keep, " ++
    "std.int.set.empty E2, std.fold Keep E2 std.int.set.add S2, " ++
    "std.fold {std.iota 200} S (x\\ s\\ r\\ (0 is x mod 3, std.int.set.remove x s r ; not (0 is x mod 3), r = s)) S3, " ++
    "std.int.set.cardinal S3 N, std.int.set.elements S3 L, L = Keep"
  match ← sols p q 1 with
  | [s] => check (hasSub s "N = 133") s!"cardinal after removal: {s}"
  | l => fail s!"expected one solution, got {l}"

-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#A map of a thousand keys is searched in logarithmic steps]]
#eval show IO Unit from do
  let p ← load ""
  let q := "std.int.map.empty E, std.fold {std.iota 1000} E (k\\ m\\ r\\ std.int.map.add k k m r) M, " ++
    "std.forall {std.iota 1000} (k\\ std.int.map.find k M k), " ++
    "M = std.map.map _ T, std.map.private.height T H, H =< 14"
  check ((← sols p q 1).length == 1) "all keys are found and the tree is balanced (height at most 14)"

-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#std.time measures a goal]]
#eval show IO Unit from do
  let p ← load ""
  match ← sols p "std.time (X = 1) T, T >= 0.0" 1 with
  | [s] => check (hasSub s "X = 1") s!"std.time keeps the goal's bindings: {s}"
  | l => fail s!"expected one solution, got {l}"
