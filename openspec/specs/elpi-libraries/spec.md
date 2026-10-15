# elpi-libraries Specification

## Purpose
The ELPI-side libraries shipped with LeanElpi and the way programs find them: a clean-room `std` library matching ELPI 1.18 behaviour, Lake-aware resolution of `accumulate` across packages, and libraries embedded in binaries.

## Requirements

### Requirement: Standard library
LeanElpi SHALL ship a clean-room standard library, written without copying upstream sources, that provides the `std` namespace of ELPI 1.18 under the same names and types, including at least the list predicates (`std.append`, `std.rev`, `std.length`, `std.mem`, `std.exists`, `std.forall`, `std.map`, `std.filter`, `std.fold`, `std.nth`, `std.split-at`, `std.zip`, `std.unzip`, `std.flatten`, `std.last`), control predicates (`std.do!`, `std.spy`, `std.assert!`, `std.findall`), the timing predicate `std.time`, and the `std.map` and `std.set` ordered-map and set structures, with their integer-keyed forms `std.int.map` and `std.int.set`. The map and set structures SHALL be height-balanced, so that adding, finding and removing a key take a number of steps logarithmic in the size. Like upstream, the standard library SHALL be available to every program without an explicit `accumulate`. Every standard predicate SHALL produce the same answers, in the same order and with the same determinism, as the ELPI 1.18 oracle, which is the reference.

#### Scenario: std list predicates behave like upstream
- **WHEN** the queries `std.append [1] [2] L`, `std.rev [1, 2, 3] R` and `std.appendR X Y [1, 2]` (all solutions) are solved
- **THEN** the answers are `L = [1, 2]`, `R = [3, 2, 1]`, and the three splits `X = [], Y = [1, 2]`, `X = [1], Y = [2]`, `X = [1, 2], Y = []` in that order, identical to the oracle
- **AND** `std.append X Y [1, 2]` has no solutions, as in the oracle, because the first two arguments of `std.append` are inputs

#### Scenario: std map operations
- **WHEN** the query `std.map.make cmp_term M0, std.map.add 1 "a" M0 M1, std.map.add 2 "b" M1 M2, std.map.find 1 M2 V` is solved
- **THEN** it succeeds with `V = "a"`, and the query `std.map.find 3 M2 W` against the same map fails
- **AND** the list combinator `std.map [1, 2] (x\ y\ y is x * 2) L` succeeds with `L = [2, 4]`

#### Scenario: Maps and sets stay ordered through removal
- **WHEN** the integers 0 to 199 are added to a `std.int.set` in descending order and the multiples of 3 are removed
- **THEN** `std.int.set.elements` returns the remaining integers in increasing order and `std.int.set.cardinal` is 133

#### Scenario: A map of a thousand keys is searched in logarithmic steps
- **WHEN** the keys 0 to 999 are added to a `std.int.map` in increasing order
- **THEN** every key is found, and the height of the tree is at most 14, the bound of a balanced tree of that size

#### Scenario: std.time measures a goal
- **WHEN** `std.time (X = 1) T` is solved
- **THEN** it succeeds with `X = 1` and a non-negative float `T`

### Requirement: Lake-aware library resolution
`accumulate` targets SHALL be resolved by a library resolver that searches, in order: the directory of the accumulating file, the include paths given explicitly (for example with `-I`), the `lib/elpi/` directory of the current Lake package, the `lib/elpi/` directories of the Lake package's dependencies in manifest order, and finally the libraries embedded in the running binary. The first match SHALL win, and an unresolved accumulation SHALL be reported with the list of directories searched.

#### Scenario: Library from a dependency package is resolved
- **WHEN** a Lake package `app` depends on package `utils`, `utils` contains `lib/elpi/utils/lists.elpi` defining `pred twice i:list A, o:list A.`, and `app` loads a program containing `accumulate utils/lists.`
- **THEN** the accumulation resolves to the file in the `utils` package under `.lake/packages/utils/lib/elpi/`, and the query `twice [1] L` succeeds

### Requirement: Embedded libraries
The ELPI sources of the shipped libraries SHALL be embedded in the compiled Lean artefacts at build time, so that the CLI, compiled executables and runtime-library users resolve them without any library file present on disk. An on-disk file of the same name found earlier in the search order SHALL take precedence over the embedded copy.

#### Scenario: Binary resolves std without files on disk
- **WHEN** the installed `lean-elpi` binary is copied to an empty directory with no `lib/elpi/` folder and runs a program whose `main` calls `std.length [a, b] N, print N`
- **THEN** the program prints `2` and exits with status 0

### Requirement: Lean API library
The library `lean`, loaded with `accumulate lean.` and shipped as `lib/elpi/lean.elpi`, SHALL declare the following, so that a program which accumulates it type checks against the Lean surface without declarations of its own:
- The reflection types: `term`, `name`, `binder`, `level` and `literal`, with all their constructors.
- The tactic types `goal` (`goal Ctx P Ty`), `decl` and `argument`.
- The signatures and modes of every `lean.*` builtin.
- Helpers written in ELPI: `copy` (structural term copy, which users can extend by adding clauses), `lean.mk_app` (application that keeps the spine flat) and `lean.subst` (instantiating a binder body).

Its declarations SHALL match exactly the encoding defined by the `lean-reflection` capability.

#### Scenario: lean library declares the term type
- **WHEN** a program accumulates `lean` and declares `pred head-const i:term, o:name.` with the clause `head-const (app (const N _) _) N.`
- **THEN** the program loads with no type errors
- **AND** the same program without `accumulate lean.` is rejected, because the type `term` and the constructor `app` are not declared

### Requirement: Tactic combinator library
The library `lean.ltac` (`lib/elpi/lean.ltac.elpi`) SHALL define `typeabbrev tactic (goal -> list goal -> prop)`, the basic tactics `lean.ltac.intro`, `lean.ltac.exact`, `lean.ltac.apply`, `lean.ltac.refine` and `lean.ltac.assumption`, and the combinators `lean.ltac.then`, `lean.ltac.thenl`, `lean.ltac.orelse`, `lean.ltac.try`, `lean.ltac.repeat` and `lean.ltac.focus`. The combinators SHALL behave like their Lean tactic counterparts:
- `then T1 T2` runs `T2` on every goal produced by `T1`.
- `thenl T Ts` runs the i-th tactic of `Ts` on the i-th goal and fails on a length mismatch.
- `orelse T1 T2` runs `T2` only if `T1` fails, and keeps no choice point into `T1`.
- `try T` never fails.
- `repeat T` applies `T` until it fails.
- `focus T` fails unless `T` closes its goal.

Proofs built through these tactics SHALL be checked by Lean as specified for ELPI tactics.

#### Scenario: then composes two tactics
- **WHEN** a tactic's `solve G _ Gs :- lean.ltac.then (lean.ltac.intro "h") lean.ltac.assumption G Gs.` is run with `by elpi intro_assume` on the goal `p → p`
- **THEN** the goal is closed with `Gs = []` and the proof term `fun h => h`

#### Scenario: orelse falls back on failure
- **WHEN** a tactic's `solve G _ Gs :- lean.ltac.orelse (lean.ltac.exact {{(0 : Nat)}}) lean.ltac.assumption G Gs.` is run on the goal `p` with `hp : p` in context
- **THEN** `exact` fails the type check, `assumption` closes the goal with `hp`, and no error is reported

### Requirement: Derive library
The library `lean.derive` (`lib/elpi/lean.derive.elpi`) SHALL provide ELPI derivers for `BEq`, `DecidableEq` and `Repr` on inductive types without indices. They generate the instance as a reflected term and add it with `lean.add_decl`. The package SHALL ship an exported command `elpi_derive <Class> <Type>` that runs these derivers. Every instance it generates SHALL be checked by the Lean kernel when it is added. Asking for a class or type shape that the derivers do not support SHALL report an error naming the unsupported case.

#### Scenario: Derived BEq instance is accepted by Lean
- **WHEN** `inductive Color | red | green` is followed by `elpi_derive BEq Color`
- **THEN** the kernel accepts an instance `BEq Color`, and `(Color.red == Color.red, Color.red == Color.green)` evaluates to `(true, false)`
