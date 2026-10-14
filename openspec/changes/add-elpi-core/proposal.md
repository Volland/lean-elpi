## Why

LeanElpi has no engine yet: before ELPI programs can manipulate Lean terms, run as tactics or certify LF proofs, Lean needs a native interpreter that runs plain ELPI 1.18 programs with the same answers, in the same order, as the upstream OCaml `elpi` binary. Milestone M1 builds that interpreter, the typechecker in front of it, and the three ways of shipping it (runtime library, CLI, compiled executables), together with the differential test harness that keeps it honest against the oracle.

## What Changes

- Add a MetaM-free λProlog engine core in Lean 4: hash-consed terms with de Bruijn levels, unification variables that carry their scope level, higher-order pattern unification (Miller's fragment) with occurs check, and hereditary Harrop goals (`pi`, `=>`, `;`, `,`, `!`, spilling `{...}`).
- Add an explicit abstract machine (goal stack, choice-point stack, cut barriers, fuel) that produces a lazy stream of solutions in ELPI's fixed depth-first, clause-order search, over a persistent substitution store (`Lean.PersistentHashMap`).
- Make the core generic over a `Backtrackable` host monad (`save`/`restore`), with a pure instance and a MetaM instance that snapshots `Meta.SavedState` at every choice point.
- Add a parser and loader for the ELPI 1.18 surface syntax: clauses, `kind`/`type`/`pred` declarations with `i:`/`o:` modes, `typeabbrev`, `accumulate`, `namespace`, clause names `:name` and grafting `:before`/`:after`, first-argument indexing.
- Add a load-time typechecker for simple types with prenex polymorphism and type abbreviations, reporting errors with source positions.
- Add core builtins (`is` arithmetic, comparison, `print`, string and I/O primitives, `fail`, `not`, `std.*` foundations) and the first solver-API tier: Lean builtin predicates declared with `@[elpi_builtin "name" "pred sig."]` and collected through an environment extension.
- Add the runtime library for ordinary Lean programs: `Elpi.solve`, `Elpi.solveIO`, `Elpi.solveAs`, `Elpi.Program.load`, `Elpi.Program.loadFile`, persistent `p.assert`, `p.withBuiltin`, and the `elpi_program` command that elaborates a program into a `foo.compiled` constant.
- Add the ELPI-side standard library (`std`) with Lake-aware library resolution and embedding into binaries.
- Add the `lean-elpi` CLI with upstream-compatible flags (`-exec`, `-test`, `-I`, `--`), a `--lean-env` option, a REPL, and `elpi_main` for precompiled executables.
- Add the conformance harness: a shared corpus run on both engines, differential answer comparison, oracle version pinning to ELPI 1.18.x, and a known-divergence register.

## Capabilities

### New Capabilities

- `elpi-core-engine`: terms, higher-order pattern unification, hereditary Harrop goals, cut, spilling, grafting, accumulate and namespaces, indexing, the abstract machine and persistent store, the monad-generic core, and core builtins.
- `elpi-typechecker`: `kind`/`type`/`pred` signatures, modes, prenex polymorphism, `typeabbrev`, and positioned load-time type errors.
- `elpi-solver-api`: tier T2 of the solver API, Lean builtin predicates registered by attribute (tiers T1, T3 and T4 arrive in `add-elpi-constraints`).
- `elpi-runtime-library`: pure, IO and typed queries over compiled programs; runtime loading, persistent extension and runtime builtins.
- `elpi-libraries`: the ELPI `std` library, Lake-aware library resolution and embedded libraries.
- `elpi-cli`: the `lean-elpi` binary, include paths, Lean environment loading, the REPL and compiled program executables.
- `elpi-conformance`: the shared corpus, differential comparison against the ELPI 1.18 oracle, version pinning and the divergence register.

### Modified Capabilities

None. This is the first change; no capability exists in `openspec/specs/` yet.

## Impact

**Milestone:** M1. Depends on no earlier change; `add-elpi-constraints` (M2), `add-lean-integration` (M3) and `add-elpi-lf` build on it.

**Motivating decisions** (tg.md): [[decisions#Native Lean engine]], [[decisions#ELPI 1.18 dialect]], [[decisions#Persistent store]], [[decisions#Explicit abstract machine]], [[decisions#Tiered solver API]], [[decisions#Monad-generic core and packaging]], [[decisions#Staged language surface]], [[decisions#Clean-room Apache license]], [[decisions#Specs before code]].

**Constraints honoured:** [[constraints#Oracle is ELPI 1.18]], [[constraints#Upstream ELPI is LGPL]], [[constraints#Lean toolchain 4.35]], [[constraints#Pattern unification is decidable]], [[constraints#MetaM is not callable from C]].

**Components introduced:** [[components#Term store]], [[components#Parser]], [[components#Type checker]], [[components#Unifier]], [[components#Persistent substitution]], [[components#Clause index]], [[components#Abstract machine]], [[components#Core builtins]], [[components#Solver registry]], [[components#Standard library]], [[components#Runtime API]], [[components#Library resolver]], [[components#CLI]], [[components#Conformance harness]].

**Other tg.md sections touched:** [[changes#add-elpi-core]], [[uml#Core class diagram]], [[uml#Machine state diagram]], [[uml#Query sequence]], [[architecture#Module map]], and the papers `engine.md` and `system.md` (their `openspec:` frontmatter gains the capabilities above).

**Code:** new modules under `Elpi/Core/`, `Elpi/Solver/`, `Elpi/Std/`, `Elpi/Runtime/`, `Elpi/Cli/`, `Elpi/Lean/Libraries.lean`, the ELPI file `lib/elpi/std.elpi`, tests under `tests/`, and the corpus and runner under `tests/conformance/`. New Lake executable target `lean-elpi`. No new Lake dependencies (no Mathlib); the opam `elpi` 1.18.x binary is a test-only dependency.

**Requirements added:**

- `elpi-core-engine`: [[openspec:elpi-core-engine#Term representation]], [[openspec:elpi-core-engine#Higher-order pattern unification]], [[openspec:elpi-core-engine#Hereditary Harrop goals]], [[openspec:elpi-core-engine#Cut]], [[openspec:elpi-core-engine#Persistent store]], [[openspec:elpi-core-engine#Abstract machine]], [[openspec:elpi-core-engine#Depth-first search order]], [[openspec:elpi-core-engine#Spilling]], [[openspec:elpi-core-engine#Clause names and grafting]], [[openspec:elpi-core-engine#Accumulate and namespaces]], [[openspec:elpi-core-engine#First-argument indexing]], [[openspec:elpi-core-engine#Monad-generic engine]], [[openspec:elpi-core-engine#Core builtins]]
- `elpi-typechecker`: [[openspec:elpi-typechecker#Signature declarations]], [[openspec:elpi-typechecker#Mode declarations]], [[openspec:elpi-typechecker#Prenex polymorphism]], [[openspec:elpi-typechecker#Type abbreviations]], [[openspec:elpi-typechecker#Load-time type errors with positions]]
- `elpi-solver-api`: [[openspec:elpi-solver-api#Lean builtin predicates]], [[openspec:elpi-solver-api#Attribute registration]]
- `elpi-runtime-library`: [[openspec:elpi-runtime-library#Pure lazy queries]], [[openspec:elpi-runtime-library#IO queries]], [[openspec:elpi-runtime-library#Typed query decoding]], [[openspec:elpi-runtime-library#Compiled program constants]], [[openspec:elpi-runtime-library#Runtime program loading]], [[openspec:elpi-runtime-library#Persistent program extension]], [[openspec:elpi-runtime-library#Runtime builtins]]
- `elpi-libraries`: [[openspec:elpi-libraries#Standard library]], [[openspec:elpi-libraries#Lake-aware library resolution]], [[openspec:elpi-libraries#Embedded libraries]]
- `elpi-cli`: [[openspec:elpi-cli#Upstream-compatible command line]], [[openspec:elpi-cli#Include paths]], [[openspec:elpi-cli#Lean environment loading]], [[openspec:elpi-cli#Interactive REPL]], [[openspec:elpi-cli#Compiled program executables]]
- `elpi-conformance`: [[openspec:elpi-conformance#Shared conformance corpus]], [[openspec:elpi-conformance#Differential answer comparison]], [[openspec:elpi-conformance#Oracle version pinning]], [[openspec:elpi-conformance#Known divergence register]]
