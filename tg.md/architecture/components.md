---
type: Component
openspec: [elpi-core-engine, elpi-typechecker, elpi-constraints, elpi-solver-api, lean-reflection, lean-integration, elpi-runtime-library, elpi-libraries, elpi-cli, elpi-conformance, elpi-lf]
---
# Components

One section per module or tool of LeanElpi. Each states what it owns, its source file, and typed edges to the components it depends on, the decisions that shape it and the change that introduces it.

Diagrams of how these fit together are in [[uml]]; the layer view is in [[architecture#Layers]]. Source files exist as a skeleton today. Each module carries a `-- @lat:` comment pointing at its section here, because `tg` resolves links from docs into `.lean` files only in the code-to-doc direction. Modules gain `implements` edges as each requirement is built.

## Term store

The term datatype: constants, de Bruijn-level bound variables, applications, λ, unification variables with scope levels, literals and opaque host data. Source: `Elpi/Core/Term.lean`.

Terms coming from Lean are hash-consed, so reflected `Expr`s share structure.

- module:: Elpi.Core.Term
- milestone:: M1
- motivated_by:: [[decisions#Explicit abstract machine]]
- motivated_by:: [[glossary#Unification variable]]
- introduced_by:: [[changes#add-elpi-core]]

## Parser

Lexer and parser for ELPI 1.18 source, producing clauses and declarations with source positions. Source: `Elpi/Core/Parser.lean`.

Positions are mapped through an offset table so inline sources embedded in Lean files report errors at the right Lean location.

- module:: Elpi.Core.Parser
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- introduced_by:: [[changes#add-elpi-core]]

## Type checker

Load-time checker for `kind`, `type`, `pred` with modes, prenex polymorphism and `typeabbrev`. Source: `Elpi/Core/Typecheck.lean`.

- module:: Elpi.Core.Typecheck
- milestone:: M1
- depends_on:: [[components#Parser]]
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
- introduced_by:: [[changes#add-elpi-core]]

## Unifier

Higher-order pattern unification with occurs check, pruning and scope checks; stuck problems go to hooks or become delayed goals. Source: `Elpi/Core/Unify.lean`.

- module:: Elpi.Core.Unify
- milestone:: M1
- depends_on:: [[components#Term store]]
- depends_on:: [[components#Persistent substitution]]
- motivated_by:: [[constraints#Pattern unification is decidable]]
- motivated_by:: [[glossary#Pattern fragment]]
- introduced_by:: [[changes#add-elpi-core]]

## Persistent substitution

The persistent map from uvar to term plus the `Backtrackable` class that snapshots the host monad. Source: `Elpi/Core/Store.lean`.

- module:: Elpi.Core.Store
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## Clause index

Program database with first-argument indexing, clause names and grafting, accumulate and namespaces. Source: `Elpi/Core/Index.lean`.

- module:: Elpi.Core.Index
- milestone:: M1
- depends_on:: [[components#Term store]]
- motivated_by:: [[glossary#Clause grafting]]
- introduced_by:: [[changes#add-elpi-core]]

## Abstract machine

The resolution loop: goal stack, choice-point stack, cut barriers, fuel, lazy solution stream, depth-first order. Source: `Elpi/Core/Machine.lean`.

- module:: Elpi.Core.Machine
- milestone:: M1
- depends_on:: [[components#Unifier]]
- depends_on:: [[components#Clause index]]
- depends_on:: [[components#Persistent substitution]]
- motivated_by:: [[decisions#Explicit abstract machine]]
- introduced_by:: [[changes#add-elpi-core]]

## Constraint store

Persistent store of delayed goals keyed by the variables they wait on, the wake-up queue, and slices owned by native handlers. Source: `Elpi/Core/Constraints.lean`.

- module:: Elpi.Core.Constraints
- milestone:: M2
- depends_on:: [[components#Persistent substitution]]
- depends_on:: [[components#Abstract machine]]
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[glossary#Delayed goal]]
- introduced_by:: [[changes#add-elpi-constraints]]

## CHR engine

Matches CHR rules against the constraint store, checks guards, removes or keeps constraints and schedules new goals, respecting `pi` scopes. Source: `Elpi/Core/CHR.lean`.

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

Lossless translation between `Lean.Expr` and the HOAS ELPI `term`, with universe levels as opaque handles, plus `{{ }}` quotations. Source: `Elpi/Lean/Reflect.lean`.

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

## Lean builtins

The `lean.*` builtins (`lean.infer`, `lean.defeq`, `lean.whnf`, `lean.elab`, `lean.env.find`, `lean.add_decl`, …) and the phase-restriction flag. Source: `Elpi/Lean/Builtins.lean`.

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

Checks `#lf` files: LF kinds, dependent types and objects, clause typing, and mode, coverage and termination in later stages. Source: `Elpi/LF/Check.lean`.

- module:: Elpi.LF.Check
- milestone:: LF
- depends_on:: [[components#Type checker]]
- depends_on:: [[components#Unifier]]
- motivated_by:: [[decisions#LF as the dependent extension]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF proof terms

Records an LF derivation alongside resolution, one constructor per clause, kept in the persistent store so backtracking discards it. Source: `Elpi/LF/ProofTerm.lean`.

- module:: Elpi.LF.ProofTerm
- milestone:: LF
- depends_on:: [[components#Abstract machine]]
- depends_on:: [[components#LF checker]]
- motivated_by:: [[decisions#LF as the dependent extension]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF export

Compiles LF signatures to Lean inductive families and proof terms to Lean terms, then has the kernel check them as certificates. Source: `Elpi/LF/Export.lean`.

`examples/lf/StlcExport.lean` is the hand-written target for the `stlc` signature; it passes the kernel with no axioms, which validates the encoding chosen in [[decisions#Well-scoped export with explicit contexts]].

- module:: Elpi.LF.Export
- milestone:: LF
- depends_on:: [[components#LF proof terms]]
- depends_on:: [[components#Expr reflection]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]
- introduced_by:: [[changes#add-elpi-lf]]

## LF strategies

The pluggable search-strategy interface (depth-first, bounded, iterative deepening), enabled only for LF proof search. Source: `Elpi/LF/Strategy.lean`.

- module:: Elpi.LF.Strategy
- milestone:: LF
- depends_on:: [[components#Abstract machine]]
- motivated_by:: [[decisions#Explicit abstract machine]]
- introduced_by:: [[changes#add-elpi-lf]]

## CLI

The `lean-elpi` executable: upstream-compatible flags (`-exec`, `-test`, `-I`), `--lean-env`, and a REPL. Source: `Elpi/Cli/Main.lean`.

- module:: Elpi.Cli.Main
- milestone:: M1
- depends_on:: [[components#Runtime API]]
- depends_on:: [[components#Library resolver]]
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-elpi-core]]

## Conformance harness

Runs every corpus program under the oracle and under `lean-elpi`, compares output and exit status, and honours the divergence register. Source: `tests/conformance/run.sh`, self-test `tests/conformance/selftest.sh`.

This is the one component with working code today: its `implements` and `verifies` edges to `elpi-conformance` are real. The self-test drives `run.sh` with stand-in engines (the oracle itself, a line-reversing engine, a fake 2.0.0 oracle). Fresh-variable name normalisation is still missing, so comparison is marked `confidence: partial`.

- module:: tests/conformance
- milestone:: M1
- depends_on:: [[components#CLI]]
- motivated_by:: [[constraints#Oracle is ELPI 1.18]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- introduced_by:: [[changes#add-elpi-core]]
