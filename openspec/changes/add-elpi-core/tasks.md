## 1. Project scaffold

- [ ] 1.1 Verify the existing scaffold under `Elpi/` (`lakefile.lean`, `lean-toolchain` = `leanprover/lean4:v4.35.0`, root module `Elpi.lean`, Apache-2.0 `LICENSE`, no Mathlib) and add the library targets `Elpi.Core`, `Elpi.Solver`, `Elpi.Std`, `Elpi.Runtime`, `Elpi.Lean`, `Elpi.Cli` and the executable target `lean-elpi`
- [ ] 1.2 Add the `tests/` Lake test driver that builds every `tests/**/*.lean` file as `#guard_msgs` golden tests, and wire it to `lake test`
- [ ] 1.3 Add a CI check that the import closure of `Elpi/Core/*.lean` contains no `Lean.Meta` or `Lean.Elab` module
- [ ] 1.4 Add a CONTRIBUTING note on the clean-room policy: no reading or copying of upstream ELPI sources; behaviour comes from documentation, papers and oracle runs

## 2. Term and store

- [ ] 2.1 Implement `ConstId` interning, `UVarId`, `Literal`, `Opaque`, `Term` (de Bruijn levels, cached hash) and `UVarInfo` in `Elpi/Core/Term.lean`
- [ ] 2.2 Implement the level-relocating `move` and β-reduction of uvar assignments at depth `d` in `Elpi/Core/Term.lean`
- [ ] 2.3 Implement `Elpi.LazyList` (`nil | cons a (Thunk tail)`) with `take`, `toList` and `head?` in `Elpi/Core/Term.lean`
- [ ] 2.4 Implement `Store` (`PersistentHashMap UVarId Term`, `PersistentArray UVarInfo`, fresh-variable counter, `delayed` list) with `deref`, `assign` and `fresh` in `Elpi/Core/Store.lean`
- [ ] 2.5 Implement `class Backtrackable (m) (σ : outParam Type)` with `save`/`restore`, and the instances for `Id`, `StateM ρ` and `IO` in `Elpi/Core/Store.lean`
- [ ] 2.6 Implement the `MetaM` instance (`Meta.saveState` / `SavedState.restore`) in `Elpi/Lean/Builtins.lean`, outside the core
- [ ] 2.7 Annotate `Elpi.Term` in `Elpi/Core/Term.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Term representation]]`
- [ ] 2.8 Annotate `Elpi.Store` in `Elpi/Core/Store.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Persistent store]]`
- [ ] 2.9 Annotate `Elpi.Backtrackable` in `Elpi/Core/Store.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Monad-generic engine]]`
- [ ] 2.10 Write test in `tests/Core/Term.lean` proving "Bound variables use de Bruijn levels" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Term representation#Bound variables use de Bruijn levels]]`
- [ ] 2.11 Write test in `tests/Core/Term.lean` proving "Unification variables carry their scope level" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Term representation#Unification variables carry their scope level]]`
- [ ] 2.12 Write test in `tests/Core/Store.lean` proving "Backtracking restores the substitution" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Backtracking restores the substitution]]`
- [ ] 2.13 Write test in `tests/Core/Store.lean` proving "Choice point restores host monad state" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Persistent store#Choice point restores host monad state]]`
- [ ] 2.14 Write test in `tests/Core/Monad.lean` proving "Core runs without MetaM" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Monad-generic engine#Core runs without MetaM]]`
- [ ] 2.15 Write test in `tests/Core/Monad.lean` proving "MetaM instance rewinds metavariable assignments" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Monad-generic engine#MetaM instance rewinds metavariable assignments]]`

## 3. Parser

- [ ] 3.1 Implement the lexer (identifiers, variables, `_`, numbers, strings, `%` and `/* */` comments, `\` binders) with source positions in `Elpi/Core/Parser.lean`
- [ ] 3.2 Implement the Pratt parser for the ELPI 1.18 fixed operator table (`:-`, `=>`, `,`, `&`, `;`, `=`, `is`, arithmetic and comparison operators, `::`, list syntax `[a, b | T]`, `{...}` spilling, `x\ t`)
- [ ] 3.3 Parse directives: `kind`, `type`, `pred` with `i:`/`o:` modes, `typeabbrev`, `accumulate`, `namespace n { }`, clause attributes `:name`/`:before`/`:after`/`:index(...)` (the latter ignored with a warning), and reject `macro`, `declare_constraint` and `constraint` blocks with an unsupported-in-M1 error
- [ ] 3.4 Implement `Elpi.Parser.loadUnits`: accumulate resolution via the library resolver, load-once by canonical path, namespace qualification and short-name resolution
- [ ] 3.5 Implement `Elpi.Parser.elimSpilling`: rewrite `p {q X}` to `q X V, p V` with `V` fresh at the enclosing depth, left to right
- [ ] 3.6 Annotate `Elpi.Parser.elimSpilling` in `Elpi/Core/Parser.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Spilling]]`
- [ ] 3.7 Annotate `Elpi.Parser.loadUnits` in `Elpi/Core/Parser.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Accumulate and namespaces]]`
- [ ] 3.8 Write test in `tests/Core/Spilling.lean` proving "Spilled call is solved before the enclosing goal" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Spilling#Spilled call is solved before the enclosing goal]]`
- [ ] 3.9 Write test in `tests/Core/Accumulate.lean` proving "Accumulated file is loaded once" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Accumulate and namespaces#Accumulated file is loaded once]]`
- [ ] 3.10 Write test in `tests/Core/Accumulate.lean` proving "Namespace qualifies predicate names" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Accumulate and namespaces#Namespace qualifies predicate names]]`

## 4. Typechecker

- [ ] 4.1 Implement simple types (`o`, `int`, `float`, `string`, arrows, applied kinds, type variables) and the signature table in `Elpi/Core/Typecheck.lean`
- [ ] 4.2 Implement `checkSignature` (declared kinds and constants, undeclared-constant errors), prenex `instantiate` per use and eager `expandAbbrev` with cycle detection
- [ ] 4.3 Implement `checkProgram`: typecheck every clause and query before compilation, collecting errors with `SourcePos`, expected and inferred types; return no program on error
- [ ] 4.4 Record argument modes per predicate for the machine's match-mode head unification
- [ ] 4.5 Annotate `Elpi.Typecheck.checkSignature` in `Elpi/Core/Typecheck.lean` with `-- @tg: implements:: [[openspec:elpi-typechecker#Signature declarations]]`
- [ ] 4.6 Annotate `Elpi.Typecheck.instantiate` in `Elpi/Core/Typecheck.lean` with `-- @tg: implements:: [[openspec:elpi-typechecker#Prenex polymorphism]]`
- [ ] 4.7 Annotate `Elpi.Typecheck.expandAbbrev` in `Elpi/Core/Typecheck.lean` with `-- @tg: implements:: [[openspec:elpi-typechecker#Type abbreviations]]`
- [ ] 4.8 Annotate `Elpi.Typecheck.checkProgram` in `Elpi/Core/Typecheck.lean` with `-- @tg: implements:: [[openspec:elpi-typechecker#Load-time type errors with positions]]`
- [ ] 4.9 Write test in `tests/Typecheck/Signatures.lean` proving "Undeclared constant is reported" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Signature declarations#Undeclared constant is reported]]`
- [ ] 4.10 Write test in `tests/Typecheck/Signatures.lean` proving "Kind and type declarations are accepted" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Signature declarations#Kind and type declarations are accepted]]`
- [ ] 4.11 Write test in `tests/Typecheck/Polymorphism.lean` proving "Polymorphic predicate is used at two types" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Prenex polymorphism#Polymorphic predicate is used at two types]]`
- [ ] 4.12 Write test in `tests/Typecheck/Typeabbrev.lean` proving "Abbreviation expands during checking" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Type abbreviations#Abbreviation expands during checking]]`
- [ ] 4.13 Write test in `tests/Typecheck/Errors.lean` proving "Ill-typed clause is rejected at load time" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Load-time type errors with positions#Ill-typed clause is rejected at load time]]`
- [ ] 4.14 Write test in `tests/Typecheck/Errors.lean` proving "Error reports the source position" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Load-time type errors with positions#Error reports the source position]]`

## 5. Unifier

- [ ] 5.1 Implement rigid–rigid decomposition, `lam` descent and η-expansion in `Elpi/Core/Unify.lean`
- [ ] 5.2 Implement flex–rigid pattern inversion with pruning of out-of-scope variables and level lowering, and the occurs check
- [ ] 5.3 Implement flex–flex unification (same variable: spine intersection; different variables: invert onto the higher-level one)
- [ ] 5.4 Suspend out-of-fragment problems as `DelayedProblem` entries in `Store.delayed` instead of failing
- [ ] 5.5 Implement `unifyMatch`: match mode for `i:` arguments, where only the selected clause's renamed variables may be assigned
- [ ] 5.6 Use explicit worklists for argument spines so that unification of 10^6-element lists does not overflow the native stack
- [ ] 5.7 Annotate `Elpi.unify` in `Elpi/Core/Unify.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Higher-order pattern unification]]`
- [ ] 5.8 Annotate `Elpi.unifyMatch` in `Elpi/Core/Unify.lean` with `-- @tg: implements:: [[openspec:elpi-typechecker#Mode declarations]]`
- [ ] 5.9 Write test in `tests/Core/Unify.lean` proving "Pattern problem has a most general unifier" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Pattern problem has a most general unifier]]`
- [ ] 5.10 Write test in `tests/Core/Unify.lean` proving "Occurs check rejects cyclic solution" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Occurs check rejects cyclic solution]]`
- [ ] 5.11 Write test in `tests/Core/Unify.lean` proving "Problem outside the pattern fragment is suspended" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Higher-order pattern unification#Problem outside the pattern fragment is suspended]]`
- [ ] 5.12 Write test in `tests/Typecheck/Modes.lean` proving "Input argument is matched not unified" and annotate it with `-- @tg: verifies:: [[openspec:elpi-typechecker#Mode declarations#Input argument is matched not unified]]`

## 6. Machine

- [ ] 6.1 Implement `Frame`, `ChoicePoint σ`, `Machine σ` and `Step σ` in `Elpi/Core/Machine.lean`
- [ ] 6.2 Implement `solveGoal` for `true`, `,`, `&`, `;`, `pi`, `sigma`, `=>` (frame-scoped local clauses) and atomic goals
- [ ] 6.3 Implement `cut` (truncate the choice stack to the frame's `cutTo` barrier) and `backtrack` (restore `Store` and host state via `Backtrackable.restore`, then try the next alternative in clause order)
- [ ] 6.4 Implement `run` with fuel accounting, the `outOfFuel` step and the resumable `yield`; build the pure `LazyList` and the `IO` stream on top of it
- [ ] 6.5 Resolve `Store.delayed` at solution time: unify problems that have become pattern or rigid (backtracking on failure) and attach the rest as `Solution.residual`
- [ ] 6.6 Annotate `Elpi.Machine.solveGoal` in `Elpi/Core/Machine.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Hereditary Harrop goals]]`
- [ ] 6.7 Annotate `Elpi.Machine.cut` in `Elpi/Core/Machine.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Cut]]`
- [ ] 6.8 Annotate `Elpi.Machine.run` in `Elpi/Core/Machine.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Abstract machine]]`
- [ ] 6.9 Annotate `Elpi.Machine.backtrack` in `Elpi/Core/Machine.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Depth-first search order]]`
- [ ] 6.10 Write test in `tests/Core/Harrop.lean` proving "Universal goal introduces a fresh constant" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Universal goal introduces a fresh constant]]`
- [ ] 6.11 Write test in `tests/Core/Harrop.lean` proving "Implication extends the program locally" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Implication extends the program locally]]`
- [ ] 6.12 Write test in `tests/Core/Harrop.lean` proving "Disjunction backtracks into the second branch" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Hereditary Harrop goals#Disjunction backtracks into the second branch]]`
- [ ] 6.13 Write test in `tests/Core/Cut.lean` proving "Cut prunes remaining clauses of the predicate" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Cut#Cut prunes remaining clauses of the predicate]]`
- [ ] 6.14 Write test in `tests/Core/Cut.lean` proving "Cut inside a called predicate does not escape it" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Cut#Cut inside a called predicate does not escape it]]`
- [ ] 6.15 Write test in `tests/Core/Machine.lean` proving "Deep recursion does not overflow the native stack" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Deep recursion does not overflow the native stack]]`
- [ ] 6.16 Write test in `tests/Core/Machine.lean` proving "Fuel exhaustion reports a resource error" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Fuel exhaustion reports a resource error]]`
- [ ] 6.17 Write test in `tests/Core/Machine.lean` proving "Solutions are produced lazily" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Abstract machine#Solutions are produced lazily]]`
- [ ] 6.18 Write test in `tests/Core/Search.lean` proving "Answers follow clause order" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Depth-first search order#Answers follow clause order]]`

## 7. Index

- [ ] 7.1 Implement per-predicate clause ordering with `:name`, `:before` and `:after` grafting across units, reporting unknown and duplicate names at load time, in `Elpi/Core/Index.lean`
- [ ] 7.2 Implement the first-argument index (`const`, literal, `[]`, `::`, `flex` keys) and `candidates`, which merges the key bucket with the flex bucket in clause order
- [ ] 7.3 Store the clause database as `PersistentHashMap ConstId PredDB` so that `assert` shares structure
- [ ] 7.4 Annotate `Elpi.Index.graft` in `Elpi/Core/Index.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Clause names and grafting]]`
- [ ] 7.5 Annotate `Elpi.Index.candidates` in `Elpi/Core/Index.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#First-argument indexing]]`
- [ ] 7.6 Write test in `tests/Core/Grafting.lean` proving "Clause grafted before a named clause" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Clause names and grafting#Clause grafted before a named clause]]`
- [ ] 7.7 Write test in `tests/Core/Grafting.lean` proving "Clause grafted after a named clause" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Clause names and grafting#Clause grafted after a named clause]]`
- [ ] 7.8 Write test in `tests/Core/Index.lean` proving "Clauses with a non-matching first argument are skipped" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#First-argument indexing#Clauses with a non-matching first argument are skipped]]`

## 8. Builtins

- [ ] 8.1 Implement `BuiltinSig`, `Builtin m` (dereferenced inputs, `m (LazyList (Array Term))` result) and the builtin choice-point cursor in `Elpi/Core/Builtins.lean`
- [ ] 8.2 Implement the core builtins: `is` (integer and float arithmetic, `^`), comparisons, `fail`, `not`, `true`, `print`, `term_to_string`, `halt`, `size`, `substring`, `int_to_string`, `rex_match`, `var`, `name`, with runtime errors on unassigned or ill-typed operands
- [ ] 8.3 Implement OCaml-compatible printing of terms, floats and strings so that output matches the oracle
- [ ] 8.4 Implement the `@[elpi_builtin "name" "sig"]` attribute, signature parsing and typechecking at attribute time, the persistent environment extension and duplicate-name errors in `Elpi/Solver/Registry.lean`
- [ ] 8.5 Annotate `Elpi.Builtins.core` in `Elpi/Core/Builtins.lean` with `-- @tg: implements:: [[openspec:elpi-core-engine#Core builtins]]`
- [ ] 8.6 Annotate `Elpi.Builtin` in `Elpi/Core/Builtins.lean` with `-- @tg: implements:: [[openspec:elpi-solver-api#Lean builtin predicates]]`
- [ ] 8.7 Annotate `Elpi.elpiBuiltinAttr` in `Elpi/Solver/Registry.lean` with `-- @tg: implements:: [[openspec:elpi-solver-api#Attribute registration]]`
- [ ] 8.8 Write test in `tests/Core/Builtins.lean` proving "Arithmetic evaluation with is" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Core builtins#Arithmetic evaluation with is]]`
- [ ] 8.9 Write test in `tests/Core/Builtins.lean` proving "Printing and string builtins" and annotate it with `-- @tg: verifies:: [[openspec:elpi-core-engine#Core builtins#Printing and string builtins]]`
- [ ] 8.10 Write test in `tests/Solver/Builtins.lean` proving "Builtin signature is typechecked" and annotate it with `-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin signature is typechecked]]`
- [ ] 8.11 Write test in `tests/Solver/Builtins.lean` proving "Builtin returns a stream of solutions" and annotate it with `-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin returns a stream of solutions]]`
- [ ] 8.12 Write test in `tests/Solver/Builtins.lean` proving "Builtin runs in the host monad" and annotate it with `-- @tg: verifies:: [[openspec:elpi-solver-api#Lean builtin predicates#Builtin runs in the host monad]]`
- [ ] 8.13 Write test in `tests/Solver/Registration.lean` proving "Solver from an imported module is available" and annotate it with `-- @tg: verifies:: [[openspec:elpi-solver-api#Attribute registration#Solver from an imported module is available]]`

## 9. Runtime API

- [ ] 9.1 Implement `CompiledProgram`, `Query`, `Solution` and `ElpiError` in `Elpi/Runtime/Api.lean`
- [ ] 9.2 Implement `Elpi.solve`, `Elpi.solveIO`, `Elpi.solveAs` and the `FromElpi` class with instances for `Nat`, `Int`, `String`, `Bool`, `Float`, `List`, `Option`, products and terms
- [ ] 9.3 Implement `Elpi.Program.load`, `Elpi.Program.loadFile`, `CompiledProgram.assert` and `CompiledProgram.withBuiltin`
- [ ] 9.4 Implement the `elpi_program foo` command (string and file forms) in `Elpi/Lean/Commands.lean`, emitting `foo.compiled` through a derived `ToExpr` instance and reporting parse and type errors at the command
- [ ] 9.5 Expose a parser invocation counter used by tests to prove that compiled programs are not parsed at runtime
- [ ] 9.6 Annotate `Elpi.solve` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Pure lazy queries]]`
- [ ] 9.7 Annotate `Elpi.solveIO` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#IO queries]]`
- [ ] 9.8 Annotate `Elpi.solveAs` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Typed query decoding]]`
- [ ] 9.9 Annotate `Elpi.elabElpiProgram` in `Elpi/Lean/Commands.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Compiled program constants]]`
- [ ] 9.10 Annotate `Elpi.Program.load` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Runtime program loading]]`
- [ ] 9.11 Annotate `Elpi.CompiledProgram.assert` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Persistent program extension]]`
- [ ] 9.12 Annotate `Elpi.CompiledProgram.withBuiltin` in `Elpi/Runtime/Api.lean` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Runtime builtins]]`
- [ ] 9.13 Write test in `tests/Runtime/Solve.lean` proving "Query is a pure function" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Pure lazy queries#Query is a pure function]]`
- [ ] 9.14 Write test in `tests/Runtime/Solve.lean` proving "Only demanded solutions are computed" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Pure lazy queries#Only demanded solutions are computed]]`
- [ ] 9.15 Write test in `tests/Runtime/SolveIO.lean` proving "IO builtin is usable from solveIO" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#IO queries#IO builtin is usable from solveIO]]`
- [ ] 9.16 Write test in `tests/Runtime/SolveAs.lean` proving "Solutions decode to a Lean type" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed query decoding#Solutions decode to a Lean type]]`
- [ ] 9.17 Write test in `tests/Runtime/SolveAs.lean` proving "Decoding failure is reported" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed query decoding#Decoding failure is reported]]`
- [ ] 9.18 Write test in `tests/Runtime/Compiled.lean` proving "Program constant needs no parsing at runtime" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Compiled program constants#Program constant needs no parsing at runtime]]`
- [ ] 9.19 Write test in `tests/Runtime/Load.lean` proving "Syntax error is returned as a value" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Runtime program loading#Syntax error is returned as a value]]`
- [ ] 9.20 Write test in `tests/Runtime/Assert.lean` proving "Asserting a clause leaves the original program unchanged" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Persistent program extension#Asserting a clause leaves the original program unchanged]]`
- [ ] 9.21 Write test in `tests/Runtime/WithBuiltin.lean` proving "Builtin attached with withBuiltin is callable" and annotate it with `-- @tg: verifies:: [[openspec:elpi-runtime-library#Runtime builtins#Builtin attached with withBuiltin is callable]]`

## 10. Std library

- [ ] 10.1 Write `lib/elpi/std.elpi` clean-room with the ELPI 1.18 `std` list, control, `std.map` and `std.set` predicates under the upstream names and types
- [ ] 10.2 Embed `lib/elpi/std.elpi` with `include_str` in `Elpi/Std/Std.lean` and load it implicitly into every program
- [ ] 10.3 Implement `Elpi.Libraries.resolve` in `Elpi/Lean/Libraries.lean`: accumulating file's directory, `-I` paths, current package `lib/elpi/`, dependency packages' `lib/elpi/` in `lake-manifest.json` order, then embedded sources; report the searched directories on failure
- [ ] 10.4 Annotate `Elpi.Std.source` in `Elpi/Std/Std.lean` with `-- @tg: implements:: [[openspec:elpi-libraries#Standard library]]`
- [ ] 10.5 Annotate `Elpi.Libraries.resolve` in `Elpi/Lean/Libraries.lean` with `-- @tg: implements:: [[openspec:elpi-libraries#Lake-aware library resolution]]`
- [ ] 10.6 Annotate `Elpi.Std.embedded` in `Elpi/Std/Std.lean` with `-- @tg: implements:: [[openspec:elpi-libraries#Embedded libraries]]`
- [ ] 10.7 Write test in `tests/Libraries/Std.lean` proving "std list predicates behave like upstream" and annotate it with `-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#std list predicates behave like upstream]]`
- [ ] 10.8 Write test in `tests/Libraries/Std.lean` proving "std map operations" and annotate it with `-- @tg: verifies:: [[openspec:elpi-libraries#Standard library#std map operations]]`
- [ ] 10.9 Write test in `tests/Libraries/Resolve.lean` proving "Library from a dependency package is resolved" and annotate it with `-- @tg: verifies:: [[openspec:elpi-libraries#Lake-aware library resolution#Library from a dependency package is resolved]]`
- [ ] 10.10 Write test in `tests/Libraries/Embedded.lean` proving "Binary resolves std without files on disk" and annotate it with `-- @tg: verifies:: [[openspec:elpi-libraries#Embedded libraries#Binary resolves std without files on disk]]`

## 11. CLI

- [ ] 11.1 Implement `parseArgs` for `FILE...`, `-exec PRED`, `-test`, `-I DIR`, `--lean-env M1,M2`, `--fuel N` and `-- ARGS` in `Elpi/Cli/Main.lean`, with exit status 0 on success and non-zero on failure or error
- [ ] 11.2 Implement `resolveIncludes` and pass include paths to the library resolver
- [ ] 11.3 Implement `loadLeanEnv`: `importModules`, run the engine in `MetaM`, and load builtins from the registry with `evalConstCheck`; without `--lean-env`, report environment-only builtins by name with a hint
- [ ] 11.4 Implement `repl`: read queries ending in `.`, print bindings, offer further solutions, report errors without exiting, and exit 0 on end of input
- [ ] 11.5 Implement `elpi_main prog` in `Elpi/Lean/Commands.lean`, generating `def main (args : List String) : IO UInt32 := Elpi.runMain prog.compiled args`
- [ ] 11.6 Annotate `Elpi.Cli.parseArgs` in `Elpi/Cli/Main.lean` with `-- @tg: implements:: [[openspec:elpi-cli#Upstream-compatible command line]]`
- [ ] 11.7 Annotate `Elpi.Cli.resolveIncludes` in `Elpi/Cli/Main.lean` with `-- @tg: implements:: [[openspec:elpi-cli#Include paths]]`
- [ ] 11.8 Annotate `Elpi.Cli.loadLeanEnv` in `Elpi/Cli/Main.lean` with `-- @tg: implements:: [[openspec:elpi-cli#Lean environment loading]]`
- [ ] 11.9 Annotate `Elpi.Cli.repl` in `Elpi/Cli/Main.lean` with `-- @tg: implements:: [[openspec:elpi-cli#Interactive REPL]]`
- [ ] 11.10 Annotate `Elpi.elabElpiMain` in `Elpi/Lean/Commands.lean` with `-- @tg: implements:: [[openspec:elpi-cli#Compiled program executables]]`
- [ ] 11.11 Write test in `tests/Cli/Flags.lean` proving "Exec runs a predicate with arguments" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Upstream-compatible command line#Exec runs a predicate with arguments]]`
- [ ] 11.12 Write test in `tests/Cli/Flags.lean` proving "Test flag runs the main predicate" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Upstream-compatible command line#Test flag runs the main predicate]]`
- [ ] 11.13 Write test in `tests/Cli/Include.lean` proving "Include path resolves accumulate" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Include paths#Include path resolves accumulate]]`
- [ ] 11.14 Write test in `tests/Cli/LeanEnv.lean` proving "Lean builtins without an environment fail clearly" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Lean environment loading#Lean builtins without an environment fail clearly]]`
- [ ] 11.15 Write test in `tests/Cli/LeanEnv.lean` proving "Lean builtins work with --lean-env" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Lean environment loading#Lean builtins work with --lean-env]]`
- [ ] 11.16 Write test in `tests/Cli/Repl.lean` proving "REPL answers queries against loaded files" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Interactive REPL#REPL answers queries against loaded files]]`
- [ ] 11.17 Write test in `tests/Cli/ElpiMain.lean` proving "Executable starts without parsing the program" and annotate it with `-- @tg: verifies:: [[openspec:elpi-cli#Compiled program executables#Executable starts without parsing the program]]`

## 12. Conformance

- [ ] 12.1 Pin the oracle: document and script installation of opam `elpi` 1.18.x in a dedicated opam switch for CI
- [ ] 12.2 Write `tests/conformance/run.sh` with `check_oracle_version`, `run_corpus` (both engines, `-test`, per-program timeout), `compare_outputs` (timing and fresh-name normalisation, `diff -u`, exit status) and `load_divergences`
- [ ] 12.3 Create `tests/conformance/divergences.md` with the entry format (program, observed difference, reason) and record the expected M1 divergences caused by end-of-run resolution of delayed problems
- [ ] 12.4 Add harness fixtures under `tests/conformance/fixtures/` (a matching pair, a reordered pair, a fake `elpi` reporting `2.0.0`, a registered divergence) for the harness tests
- [ ] 12.5 Add corpus programs to `tests/conformance/corpus/` and compare them against the oracle: `terms.elpi` (scope levels), `pattern.elpi` (MGU, occurs check, suspended problems), `harrop.elpi` (`pi`, `=>`, `;`), `cut.elpi`, `backtrack.elpi`, `deep.elpi` (10^6 recursion), `order.elpi`, `spilling.elpi`, `grafting.elpi`, `accumulate.elpi` (with `lib/` units), `namespace.elpi`, `index.elpi`, `arith.elpi`, `strings.elpi`
- [ ] 12.6 Add typechecker corpus programs (`signatures.elpi`, `modes.elpi`, `poly.elpi`, `typeabbrev.elpi`, `type-errors.elpi`) and compare the oracle's accept/reject verdicts
- [ ] 12.7 Add library corpus programs (`std-list.elpi`, `std-map.elpi`, `std-set.elpi`, `std-control.elpi`) and compare against the oracle
- [ ] 12.8 Add a `lake run conformance` script target and run the full corpus in CI
- [ ] 12.9 Annotate the shell function `run_corpus` in `tests/conformance/run.sh` with `# @tg: implements:: [[openspec:elpi-conformance#Shared conformance corpus]]`
- [ ] 12.10 Annotate the shell function `compare_outputs` in `tests/conformance/run.sh` with `# @tg: implements:: [[openspec:elpi-conformance#Differential answer comparison]]`
- [ ] 12.11 Annotate the shell function `check_oracle_version` in `tests/conformance/run.sh` with `# @tg: implements:: [[openspec:elpi-conformance#Oracle version pinning]]`
- [ ] 12.12 Annotate the shell function `load_divergences` in `tests/conformance/run.sh` with `# @tg: implements:: [[openspec:elpi-conformance#Known divergence register]]`
- [ ] 12.13 Write test in `tests/Conformance/Harness.lean` proving "Every corpus program runs on both engines" and annotate it with `-- @tg: verifies:: [[openspec:elpi-conformance#Shared conformance corpus#Every corpus program runs on both engines]]`
- [ ] 12.14 Write test in `tests/Conformance/Harness.lean` proving "Matching answers pass" and annotate it with `-- @tg: verifies:: [[openspec:elpi-conformance#Differential answer comparison#Matching answers pass]]`
- [ ] 12.15 Write test in `tests/Conformance/Harness.lean` proving "Divergent answers fail with a diff" and annotate it with `-- @tg: verifies:: [[openspec:elpi-conformance#Differential answer comparison#Divergent answers fail with a diff]]`
- [ ] 12.16 Write test in `tests/Conformance/Harness.lean` proving "Unexpected oracle version is reported" and annotate it with `-- @tg: verifies:: [[openspec:elpi-conformance#Oracle version pinning#Unexpected oracle version is reported]]`
- [ ] 12.17 Write test in `tests/Conformance/Harness.lean` proving "Registered divergence does not fail the suite" and annotate it with `-- @tg: verifies:: [[openspec:elpi-conformance#Known divergence register#Registered divergence does not fail the suite]]`

## 13. Docs and traceability

- [ ] 13.1 Update `tg.md/papers/engine.md` ("A Persistent Abstract Machine for Lambda Prolog") to describe the implemented term representation, store, unifier and machine, and add `openspec: [elpi-core-engine, elpi-typechecker]` to its frontmatter
- [ ] 13.2 Update `tg.md/papers/system.md` ("LeanElpi: Embedding Lambda Prolog in Lean 4") with the runtime library, CLI, libraries and conformance story, and add `openspec: [elpi-runtime-library, elpi-cli, elpi-libraries, elpi-conformance]` to its frontmatter
- [ ] 13.3 Update `tg.md/papers/solvers.md` ("Writing Your Own Solver") with the tier T2 builtin API and add `openspec: [elpi-solver-api]` to its frontmatter
- [ ] 13.4 Update `tg.md/architecture/components.md` so that each component introduced here (Term store, Parser, Type checker, Unifier, Persistent substitution, Clause index, Abstract machine, Core builtins, Solver registry, Standard library, Runtime API, Library resolver, CLI, Conformance harness) links its implemented module, and mark them `introduced_by:: [[changes#add-elpi-core]]`
- [ ] 13.5 Update `tg.md/architecture/uml.md` so that the "Core class diagram", "Machine state diagram" and "Query sequence" sections match the diagrams in this change's `design.md`
- [ ] 13.6 Update `tg.md/changes.md#add-elpi-core` with the delivered status and add any new design decision recorded during implementation to `tg.md/decisions.md`
- [ ] 13.7 Run `tg check` and fix every broken wiki link, code reference and annotation it reports
- [ ] 13.8 Run `tg trace elpi-core-engine elpi-typechecker elpi-solver-api elpi-runtime-library elpi-libraries elpi-cli elpi-conformance --gaps` and close every gap it reports: each requirement has an `implements` annotation and each scenario has a `verifies` annotation on a passing test
- [ ] 13.9 Run `openspec validate add-elpi-core --strict`, `lake build`, `lake test` and `tests/conformance/run.sh`, and confirm all pass
