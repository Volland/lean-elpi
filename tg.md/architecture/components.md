---
type: Component
openspec: [elpi-core-engine, elpi-typechecker, elpi-constraints, elpi-solver-api, lean-reflection, lean-integration, elpi-runtime-library, elpi-libraries, elpi-cli, elpi-conformance, elpi-lf, lean-interop, language-bindings]
---
# Components

One section per module or tool of LeanElpi. Each states what it owns, its source file, and typed edges to the components it depends on, the decisions that shape it and the change that introduces it.

Diagrams of how these fit together are in [[uml]]; the layer view is in [[architecture#Layers]]. All modules are implemented (see each section). Each module carries a `-- @lat:` comment pointing at its section here, because `tg` resolves links from docs into `.lean` files only in the code-to-doc direction. Modules gain `implements` edges as each requirement is built.

## Term store

The term datatype: constants, de Bruijn-level bound variables, applications, λ, unification variables with scope levels, literals and opaque host data. Source: `Elpi/Core/Term.lean`.

Terms coming from Lean are hash-consed, so reflected `Expr`s share structure.

`renameCVars` (clause instantiation) keeps every subterm that does not change as the same object, so a clause body's ground parts are never copied; `Term.sameRef` is the pointer test. `applyAtFrom` relocates a λ-term from the level it was bound at while β-reducing it, one traversal where `shiftUp` then `applyAt` took two. Sharing in `subst`/`substN`/`shiftUp` was measured and rejected: their input is usually a fresh term that Lean updates in place, and keeping the original alive for the pointer test stops that ([[decisions#Allocate less than OCaml]]).

- module:: Elpi.Core.Term
- milestone:: M1
- motivated_by:: [[decisions#Explicit abstract machine]]
- motivated_by:: [[glossary#Unification variable]]
- introduced_by:: [[changes#add-elpi-core]]
- changed_by:: [[changes#optimize-clause-selection]]

## Parser

Lexer and parser for ELPI 1.18 source, producing clauses and declarations with source positions. Source: `Elpi/Core/Parser.lean`.

Positions are mapped through an offset table so inline sources embedded in Lean files report errors at the right Lean location.

Three syntax forms are rewritten on the token stream before parsing, so the parser itself stays small: `macro @name X :- body.` definitions and their uses (`expandMacros`), and `pi x y\ body` / `sigma x y\ body`, which stand for nested single-name binders (`expandBinders`). The lexer also accepts blanks before a binder's backslash (not after `rule`, where a spaced backslash separates CHR heads), a trailing comma in a list, and an `:index` attribute before a declaration.

- module:: Elpi.Core.Parser
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- introduced_by:: [[changes#add-elpi-core]]

## Type checker

Load-time checker for `kind`, `type`, `pred` with modes, prenex polymorphism and `typeabbrev`. Source: `Elpi/Core/Typecheck.lean`.

A program that declares no kinds, types or predicates of its own is checked as the oracle checks it: an undeclared constant is implicitly declared and reported as a warning, which the CLI prints. Once a program declares types, an undeclared constant is an error ([[decisions#Undeclared constants are an error only where the type is known]]).

- module:: Elpi.Core.Typecheck
- milestone:: M1
- depends_on:: [[components#Parser]]
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
- introduced_by:: [[changes#add-elpi-core]]

## Unifier

Higher-order pattern unification with occurs check, pruning and scope checks; stuck problems go to hooks or become delayed goals. Source: `Elpi/Core/Unify.lean`.

The worklist holds `Eqn` records (one object per equation) and drops a pair whose two sides are the same object, which renaming with sharing makes common.

- module:: Elpi.Core.Unify
- milestone:: M1
- depends_on:: [[components#Term store]]
- depends_on:: [[components#Persistent substitution]]
- motivated_by:: [[constraints#Pattern unification is decidable]]
- motivated_by:: [[glossary#Pattern fragment]]
- introduced_by:: [[changes#add-elpi-core]]
- changed_by:: [[changes#optimize-clause-selection]]

## Persistent substitution

The store of unification variables (bindings in arrays with an undo trail, checkpoints for choice points) plus the `Backtrackable` class that snapshots the host monad. Source: `Elpi/Core/Store.lean`.

- module:: Elpi.Core.Store
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## Clause index

Program database with first-argument indexing, clause names and grafting, accumulate and namespaces. Source: `Elpi/Core/Index.lean`.

A clause is compiled when it enters a `PredDB`: `args` holds the head's arguments and `goals` the body with top-level `,` split and `true` dropped. The candidate array of each first-argument key already includes the variable-headed clauses in clause order (`PredDB.ofArray` builds them in one pass, `push` appends), so `candidates` returns a stored array and allocates nothing, like ELPI's `get_clauses`.

A predicate declared with `:index (d1 … dn)` keeps that specification in its `PredDB` and in the machine's environment. A call then takes the first-argument bucket and drops the clauses (and hypotheses) whose indexed arguments rigidly clash with the call's within `di` levels (`PredDB.select`, `idxMatch`); a hash of each ground indexed argument, stored with the clause, makes the common case one comparison. Variables and λ-terms never clash, so the specification changes how many clauses are tried, not the answers.

- module:: Elpi.Core.Index
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[glossary#Clause grafting]]
- introduced_by:: [[changes#add-elpi-core]]
- changed_by:: [[changes#optimize-clause-selection]]

## Abstract machine

The resolution loop: goal stack, choice-point stack, cut barriers, fuel, lazy solution stream, depth-first order. Source: `Elpi/Core/Machine.lean`.

A call keeps its candidates as two arrays, the matching hypotheses and the index's static array, which the choice point shares rather than copies. Head matching returns one `HM` record per step and keeps clause variables in an `Array Term` with the placeholder `unsetVar`, instead of `Option` boxes inside nested pairs. A selected clause pushes one frame per compiled body goal, each with the call's cut barrier.

- module:: Elpi.Core.Machine
- milestone:: M1
- depends_on:: [[components#Unifier]]
- depends_on:: [[components#Clause index]]
- depends_on:: [[components#Persistent substitution]]
- motivated_by:: [[decisions#Explicit abstract machine]]
- introduced_by:: [[changes#add-elpi-core]]
- changed_by:: [[changes#optimize-clause-selection]]

## Constraint store

Persistent store of delayed goals keyed by the variables they wait on, the wake-up queue, and slices owned by native handlers. Source: `Elpi/Core/Constraints.lean`, held in `Store.cstore` so choice points capture it.

The same file defines `Locals`, the hypotheses added by `=>`: the ordered list (for CHR contexts and constraint snapshots) and persistent maps by predicate, by predicate and first-argument key, and of variable-keyed hypotheses. `Locals.candidates` merges the last two by insertion order, so a call never looks at hypotheses that cannot apply.

- module:: Elpi.Core.Constraints
- milestone:: M2
- depends_on:: [[components#Persistent substitution]]
- depends_on:: [[components#Abstract machine]]
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[glossary#Delayed goal]]
- introduced_by:: [[changes#add-elpi-constraints]]
- changed_by:: [[changes#optimize-clause-selection]]

## CHR engine

Matches CHR rules against the constraint store, checks guards, removes or keeps constraints and schedules new goals, respecting `pi` scopes. Source: `Elpi/Core/CHR.lean` (matching) and `activate` in `Elpi/Core/Machine.lean` (guards and firing).

- module:: Elpi.Core.CHR
- milestone:: M2
- depends_on:: [[components#Constraint store]]
- motivated_by:: [[glossary#Constraint Handling Rules]]
- introduced_by:: [[changes#add-elpi-constraints]]

## Core builtins

Arithmetic (`is`, `calc`), comparison, strings, `print`, `var`, `same_var`, `fail`, `halt`, and the other builtins every program expects. Source: `Elpi/Core/Builtins.lean`.

- module:: Elpi.Core.Builtins
- milestone:: M1
- depends_on:: [[components#Abstract machine]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- introduced_by:: [[changes#add-elpi-core]]

## Solver registry

Environment extension and attributes (`@[elpi_builtin]`, `@[elpi_constraint_handler]`, `@[elpi_unif_hook]`) that make solvers from any imported module available. Source: `Elpi/Solver/Registry.lean`.

- module:: Elpi.Solver.Registry
- milestone:: M1
- depends_on:: [[components#Core builtins]]
- motivated_by:: [[decisions#Tiered solver API]]
- introduced_by:: [[changes#add-elpi-core]]

## Standard library

The clean-room `std` library: lists, maps, sets, strings, `findall`, `spy`, `assert!`, with upstream predicate names. Source: `Elpi/Std/Std.lean` and `lib/elpi/std.elpi`.

`std.map K V` is a height-balanced (AVL) tree that carries its comparison function, `std.set` is a map to `unit`, and `std.int.map` / `std.int.set` fix the key type; all are ELPI source, written from the textbook algorithm. `std.time G T` measures a goal with the `gettimeofday` builtin. The embedded files are inputs of the library in the lakefile, so editing `lib/elpi` rebuilds it. Insert, find and remove for integer keys (`std.int.map`, `std.int.set`) run natively in Lean on the same trees (`IntAvl` in `Elpi/Core/Builtins.lean`), because interpreting the balancing costs a few hundred resolution steps per key; a map ordered by another comparison uses the library code.

- module:: Elpi.Std.Std
- milestone:: M1
- depends_on:: [[components#Core builtins]]
- motivated_by:: [[decisions#Clean-room Apache license]]
- introduced_by:: [[changes#add-elpi-core]]

## Runtime API

The library for ordinary Lean programs: pure lazy `Elpi.solve`, `solveIO`, `solveAs`, program loading, persistent `assert`, `withBuiltin`. Source: `Elpi/Runtime/Api.lean`.

- module:: Elpi.Runtime.Api
- milestone:: M1
- depends_on:: [[components#Abstract machine]]
- depends_on:: [[components#Type checker]]
- depends_on:: [[components#Solver registry]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## Rule DSL

`elpi_rules` blocks: clauses written in Lean syntax, typechecked at compile time against `deriving Elpi` signatures, compiled to a program constant. Source: `Elpi/Runtime/Dsl.lean`.

- module:: Elpi.Runtime.Dsl
- milestone:: M3
- depends_on:: [[components#Runtime API]]
- depends_on:: [[components#Marshalling]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-lean-integration]]

## Expr reflection

Lossless translation between `Lean.Expr` and the HOAS ELPI `term`, with universe levels as opaque handles, plus `{{ }}` quotations. Source: `Elpi/Lean/Reflect.lean` (reflection) and `Elpi/Lean/Quote.lean` (quotations).

- module:: Elpi.Lean.Reflect
- milestone:: M3
- depends_on:: [[components#Term store]]
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
- motivated_by:: [[decisions#Lossless reflection with opaque levels]]
- introduced_by:: [[changes#add-lean-integration]]

## Marshalling

`ToElpi`/`FromElpi` classes, instances for core types, and the `deriving Elpi` handler that also emits `kind`/`type` declarations. Source: `Elpi/Lean/Marshal.lean`.

- module:: Elpi.Lean.Marshal
- milestone:: M3
- depends_on:: [[components#Term store]]
- motivated_by:: [[glossary#Marshalling]]
- introduced_by:: [[changes#add-lean-integration]]

## Type interoperability

The two-way type bridge: `elpi_data` (ELPI declarations to Lean inductives), `elpi_extern` (typed Lean functions as ELPI predicates) and `#elpi_signature`. Source: `Elpi/Lean/Interop.lean`; parametric `deriving Elpi` is in `Elpi/Lean/Marshal.lean`.

- module:: Elpi.Lean.Interop
- milestone:: Interop
- depends_on:: [[components#Marshalling]]
- depends_on:: [[components#Solver registry]]
- depends_on:: [[components#Commands]]
- motivated_by:: [[decisions#Two-way type bridge]]
- introduced_by:: [[changes#add-lean-interop]]

## Lean builtins

The `lean.*` builtins (`lean.infer`, `lean.defeq`, `lean.whnf`, `lean.elab`, `lean.env.find`, `lean.env.indt`, `lean.add_decl`, `lean.add_inductive`, …) and the phase-restriction flag. Source: `Elpi/Lean/Builtins.lean`.

- module:: Elpi.Lean.Builtins
- milestone:: M3
- depends_on:: [[components#Expr reflection]]
- depends_on:: [[components#Solver registry]]
- motivated_by:: [[decisions#Coq-Elpi style integration surface]]
- motivated_by:: [[glossary#Phase restriction]]
- introduced_by:: [[changes#add-lean-integration]]

## Commands

Lean commands `elpi_program`, `elpi_db`, `elpi_accumulate`, `#elpi`, `elpi_command`, `elpi_export`, `elpi_main`, and the environment extension holding programs. Source: `Elpi/Lean/Commands.lean`.

- module:: Elpi.Lean.Commands
- milestone:: M3
- depends_on:: [[components#Runtime API]]
- depends_on:: [[components#Lean builtins]]
- depends_on:: [[components#Library resolver]]
- motivated_by:: [[decisions#Coq-Elpi style integration surface]]
- introduced_by:: [[changes#add-lean-integration]]

## Tactic bridge

`elpi_tactic` and `by elpi name args`: reflects the goal, runs `solve`, reifies the proof term, assigns the goal metavariable and returns new goals. Source: `Elpi/Lean/Tactic.lean`.

- module:: Elpi.Lean.Tactic
- milestone:: M3
- depends_on:: [[components#Commands]]
- depends_on:: [[components#Expr reflection]]
- motivated_by:: [[decisions#Coq-Elpi style integration surface]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]
- introduced_by:: [[changes#add-lean-integration]]

## Library resolver

Resolves `accumulate` names through the `lib/elpi/` folder of every Lake package and through libraries embedded in binaries. Source: `Elpi/Lean/Libraries.lean`.

- module:: Elpi.Lean.Libraries
- milestone:: M1
- depends_on:: [[components#Parser]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## LF checker

Reads and checks `#lf` files: the surface syntax and its directives, LF kinds, dependent types and objects with implicit-argument reconstruction, and the family roles. Source: `Elpi/LF/Check.lean`.

- module:: Elpi.LF.Check
- milestone:: LF
- depends_on:: [[components#Type checker]]
- depends_on:: [[components#Unifier]]
- motivated_by:: [[decisions#LF as the dependent extension]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF proof terms

Records an LF derivation during resolution: each `lf.<family>` predicate takes the proof term as its first argument, so backtracking discards partial derivations. Source: `Elpi/LF/ProofTerm.lean`.

The module also holds the bridge hook and the query driver; erasure for plain programs is `Elpi/LF/Erase.lean`.

- module:: Elpi.LF.ProofTerm
- milestone:: LF
- depends_on:: [[components#Abstract machine]]
- depends_on:: [[components#LF checker]]
- motivated_by:: [[decisions#LF as the dependent extension]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF export

Compiles LF signatures in the exportable fragment to Lean inductive families, and proof terms to fully explicit constructor applications that the kernel checks as certificates. Source: `Elpi/LF/Export.lean`.

`examples/lf/StlcExport.lean` is the hand-written target for the `stlc` signature; it passes the kernel with no axioms, which validates the encoding chosen in [[decisions#Well-scoped export with explicit contexts]].

- module:: Elpi.LF.Export
- milestone:: LF
- depends_on:: [[components#LF proof terms]]
- depends_on:: [[components#Expr reflection]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF strategies

Search strategies for LF proof search (depth-first, bounded, iterative deepening), driven by a derivation depth per LF goal and a cutoff flag in the machine. Source: `Elpi/LF/Strategy.lean`.

Iterative deepening restarts with shared fuel and reports each answer once, by proof-height window.

- module:: Elpi.LF.Strategy
- milestone:: LF
- depends_on:: [[components#Abstract machine]]
- motivated_by:: [[decisions#Explicit abstract machine]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF modes and totality

Static analyses of LF signatures: `#mode` groundness checking, world regularity, input and output coverage, structural termination, and the construction of a kernel-checked totality theorem. Source: `Elpi/LF/Mode.lean`, `Elpi/LF/Total.lean`.

The checks are diagnostics outside the trust base. A totality theorem is added only when its proof is built and accepted by the kernel; see [[decisions#No unproved totality theorems]].

- module:: Elpi.LF.Mode
- module:: Elpi.LF.Total
- milestone:: LF
- depends_on:: [[components#LF checker]]
- depends_on:: [[components#LF export]]
- motivated_by:: [[decisions#No unproved totality theorems]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF Lean commands

The LF commands `lf_signature`, `#lf_query`, `lf_export` and `lf_certify`, over an environment extension that stores signatures as source. Source: `Elpi/Lean/LFCommands.lean`.

The module also compiles bridged Lean functions to closures for the bridge hook.

- module:: Elpi.Lean.LFCommands
- milestone:: LF
- depends_on:: [[components#LF export]]
- depends_on:: [[components#Commands]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]
- introduced_by:: [[changes#add-elpi-lf]]

## CLI

The `lean-elpi` executable: upstream-compatible flags (`-exec`, `-test`, `-I`), `--lean-env`, and a REPL. Source: `Elpi/Cli/Main.lean`.

- module:: Elpi.Cli.Main
- milestone:: M1
- depends_on:: [[components#Runtime API]]
- depends_on:: [[components#Library resolver]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## C ABI

A handle-and-string C interface over the runtime API, so any language with a C FFI can load programs and run queries; answers are JSON text. Source: `Elpi/Ffi.lean`, `ffi/leanelpi.{h,c}`, `scripts/build-ffi.sh`.

Programs live in a handle table inside the Lean runtime, updated atomically, so handles can be used from several threads. The shim starts the runtime, attaches each calling thread to it and turns Lean `IO` results into error strings. `build-ffi.sh` links the engine and the Lean runtime into one shared library (macOS) or ships `libleanshared` beside it (Linux). Lean-environment builtins are not reachable through it.

- module:: Elpi.Ffi
- depends_on:: [[components#Runtime API]]
- motivated_by:: [[decisions#Handle-and-string C ABI]]
- introduced_by:: [[changes#add-language-bindings]]

## Language bindings

Python (`ctypes`), Node.js (`koffi`) and Rust packages over the C ABI, in `bindings/`, released together from one version tag by `.github/workflows/release.yml`.

Each is a thin wrapper: a `Program` class with `first`, `solve`, `ask` and persistent `assert`. Distribution is the hard part: platform wheels, per-platform npm packages with a loader, and a crate that links a library fetched separately. Versions are kept equal by `scripts/check-versions.sh`; the release steps are in `PUBLISHING.md`.

- module:: bindings
- depends_on:: [[components#C ABI]]
- motivated_by:: [[decisions#Handle-and-string C ABI]]
- introduced_by:: [[changes#add-language-bindings]]

## Conformance harness

Runs every corpus program under the oracle and under `lean-elpi`, compares output and exit status, and honours the divergence register. Source: `tests/conformance/run.sh`, self-test `tests/conformance/selftest.sh`.

This is the one component with working code today: its `implements` and `verifies` edges to `elpi-conformance` are real. The self-test drives `run.sh` with stand-in engines (the oracle itself, a line-reversing engine, a fake 2.0.0 oracle). Fresh-variable name normalisation is still missing, so comparison is marked `confidence: partial`.

- module:: tests/conformance
- milestone:: M1
- depends_on:: [[components#CLI]]
- motivated_by:: [[constraints#Oracle is ELPI 1.18]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- introduced_by:: [[changes#add-elpi-core]]

## Upstream compatibility suite

Runs ELPI 1.18's own test programs, copied under `tests/upstream/`, on `lean-elpi` and judges each by upstream's rule: exit 0 is success unless the registry expects failure or an output pattern.

`manifest.tsv` is generated from upstream's `tests/suite/*.ml` registry by `extract.py` (name, category, source, expectation, flags, stdin). `run.sh [lean|oracle]` runs it; `oracle` mode runs the real ELPI and must pass everything, which proves the copy and the runner. Failing tests are registered with their first error in `known-failures.md` and reported as `known`, or `stale` once they pass. Trace-format tests, performance categories (timed by [[components#Benchmark harness]]) and the large corpora (set `UPSTREAM_SOURCES`) are skipped. The copied sources are LGPL-2.1 (`LICENSE-ELPI`).

- module:: tests/upstream
- depends_on:: [[components#Conformance harness]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]

## Benchmark harness

Times `lean-elpi`, ELPI 1.18 and, where a program is also a Teyjus module, Teyjus on ELPI's own performance programs plus a few small ones of ours. It reports median and best wall time and peak memory per engine.

`tests/bench/run.py` runs each workload N times (default 5) under one shared stack limit, from `tests/upstream/sources` (the `performance_FO` and `performance_HO` programs) and `tests/bench/programs` (`nrev`, `fib`, `hoabs`, sized to finish on every engine). A run that exits non-zero or exceeds the timeout is recorded as that status, never as a time. Teyjus comes from `TEYJUS_BIN`; it needs OCaml below 5.0. Results are in `tests/bench/results/` (`2026-10-15.json` for 0.3.0, `2026-10-15-optimized.json` and `2026-10-15-rerun.json` after the store rewrite, `2026-10-15-clause-selection.json` after [[changes#optimize-clause-selection]], run without Teyjus; `2026-10-15-v0.3.2.json` for 0.3.2 and `2026-10-15-all-programs.json` once every program loaded) and published in four blog posts: [Compatibility and performance](site/content/blog/compatibility-and-performance.md), [Why LeanElpi was slow](site/content/blog/why-leanelpi-was-slow.md), [What we took from ELPI](site/content/blog/what-we-took-from-elpi.md) and [Every ELPI performance program runs](site/content/blog/every-performance-program-runs.md). The harness times; it does not compare answers, which is the job of the conformance suites.

- module:: tests/bench
- depends_on:: [[components#Upstream compatibility suite]]
- motivated_by:: [[papers/engine#A Persistent Abstract Machine for Lambda Prolog#Performance expectations]]
