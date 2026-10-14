## 1. Constraint store and delayed goals (core)

- [x] 1.1 Create `Elpi/Core/Constraints.lean` with `Constraint`, `ConstraintId` and the persistent `ConstraintStore` (`byId`, `byKey`, `byPred`, `handlerState`) and its operations `add`, `remove` and `wake` (design D1)
- [x] 1.2 Add `cstore` and `wakeQueue` to `Machine.State` in `Elpi/Core/Machine.lean`, and check that choice points capture both without copying
- [x] 1.3 Implement the builtin `declare_constraint Goal Keys` in `Elpi/Core/Builtins.lean`: collect the key uvars (including flexible heads), record the scope level and the local program snapshot, and add the constraint to the store
- [x] 1.4 Make the unifier (`Elpi/Core/Unify.lean`) push woken constraint ids onto `wakeQueue` when it binds a key uvar, and have the machine drain the queue before it pops the next goal (design D2)
- [x] 1.5 Route problems outside the pattern fragment through `declare_constraint`-style suspension keyed on their flexible heads, replacing the M1 suspension list
- [x] 1.6 Annotate `declare_constraint` and the wake-queue drain with `-- @tg: implements:: [[openspec:elpi-constraints#Delayed goals]]`
- [x] 1.7 Annotate `ConstraintStore` with `-- @tg: implements:: [[openspec:elpi-constraints#Backtrackable constraint store]]`

## 2. CHR engine

- [x] 2.1 Extend `Elpi/Core/Parser.lean` and `Elpi/Core/Typecheck.lean` for `constraint P1 … Pn { rule … }` blocks: optional kept heads, `\` removed heads, `| Guard`, `<=> Body`, and heads of the form `(Ctx ?- C)`
- [x] 2.2 Create `Elpi/Core/CHR.lean` with `CHRRule` and `ConstraintBlock`, plus activation driven by the active constraint: rules in source order, the active constraint tried at each head position, partners taken from `byPred` in insertion order (design D3)
- [x] 2.3 Implement freeze and thaw of uvars for one-way head matching and guard execution, where a guard runs in a nested machine run and fails if it tries to bind a frozen variable
- [x] 2.4 Implement firing: remove the `\` heads, thaw, push `Body`, and re-activate the constraints that the body adds
- [x] 2.5 Implement scoped matching: bind `Ctx` to the reified local program, and compare eigenvariables across heads by level (design D4)
- [x] 2.6 Annotate the rule activation entry point with `-- @tg: implements:: [[openspec:elpi-constraints#CHR rules]]`
- [x] 2.7 Annotate context capture and the scoped matcher with `-- @tg: implements:: [[openspec:elpi-constraints#Scoped constraints]]`

## 3. Residual constraints

- [x] 3.1 Add `constraints : List ResidualConstraint` to the solution type and fill it from `cstore` when an answer is produced, with the substitution applied and the context and keys kept
- [x] 3.2 Print residual constraints on the CLI (`Elpi/Cli/Main.lean`) after the substitution, in the ELPI 1.18 oracle's format
- [x] 3.3 Annotate the residual extraction function with `-- @tg: implements:: [[openspec:elpi-constraints#Residual constraints]]`

## 4. Solver API tiers T1, T3, T4

- [x] 4.1 Add the `leq` CHR solver as the ELPI library file `lib/elpi/leq.elpi` (reflexivity, antisymmetry, idempotence and transitivity rules), registered with `Elpi/Std/Std.lean` so `accumulate` resolves it
- [x] 4.2 Reject, at load time, CHR blocks over a predicate already owned by a native handler
- [x] 4.3 Add `ConstraintHandler`, `HandlerResult`, `Store` (read-only view with `getState`/`setState`) and the `@[elpi_constraint_handler "name"]` attribute to `Elpi/Solver/Registry.lean` (design D5)
- [x] 4.4 Dispatch handler-owned constraints to `onAdd` when they are added and to `onWake` when the wake queue is drained, and apply `simplify`/`propagate`/`fail`/`keep`
- [x] 4.5 Keep handler state as `Dynamic` in `cstore.handlerState`, and re-initialise it with a warning on a `TypeName` mismatch
- [x] 4.6 Add `UnifHook` (with its `interpreted` symbols and `onStuck`) and the `@[elpi_unif_hook]` attribute. Make the unifier return `stuck p` and consult hooks in registration order only then. Re-check `.solved θ` for occurs and scope violations, and turn `.suspend` into a delayed goal (design D6)
- [x] 4.7 Annotate the `leq` library file header (ELPI comment `% @tg: implements:: [[openspec:elpi-solver-api#CHR solvers in ELPI]]`) and the T1 loading path
- [x] 4.8 Annotate `ConstraintHandler` with `-- @tg: implements:: [[openspec:elpi-solver-api#Native constraint handlers]]`
- [x] 4.9 Annotate `UnifHook` and the hook dispatch in `Elpi/Core/Unify.lean` with `-- @tg: implements:: [[openspec:elpi-solver-api#Unification hooks]]`

## 5. Tests (one per scenario, `#guard_msgs` golden tests)

- [x] 5.1 `tests/Constraints/DelayedGoals.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#Delayed goals#Goal suspends on an unassigned variable]]` directly above it
- [x] 5.2 `tests/Constraints/DelayedGoals.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#Delayed goals#Suspended goal resumes on assignment]]`
- [x] 5.3 `tests/Constraints/Store.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#Backtrackable constraint store#Backtracking removes constraints added later]]`
- [x] 5.4 `tests/Constraints/CHR.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Simplification rule replaces constraints]]`
- [x] 5.5 `tests/Constraints/CHR.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Propagation rule adds constraints]]`
- [x] 5.6 `tests/Constraints/CHR.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#CHR rules#Failing guard prevents firing]]`
- [x] 5.7 `tests/Constraints/Scoped.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#Scoped constraints#Constraint under pi respects eigenvariables]]`
- [x] 5.8 `tests/Constraints/Residual.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-constraints#Residual constraints#Unsolved constraints are reported with the answer]]`
- [x] 5.9 `tests/Solver/CHRSolvers.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-solver-api#CHR solvers in ELPI#leq solver detects a cycle]]`
- [x] 5.10 `tests/Solver/Handlers.lean`: write the `"lia"` fixture handler and the test, and add `-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler simplifies a new constraint]]`
- [x] 5.11 `tests/Solver/Handlers.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler wakes on variable instantiation]]`
- [x] 5.12 `tests/Solver/Handlers.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-solver-api#Native constraint handlers#Handler state backtracks with the store]]`
- [x] 5.13 `tests/Solver/Hooks.lean`: write the call-counting hook fixture and the test, and add `-- @tg: verifies:: [[openspec:elpi-solver-api#Unification hooks#Hook is consulted only when unification is stuck]]`
- [x] 5.14 `tests/Solver/Hooks.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-solver-api#Unification hooks#Hook cannot override syntactic success]]`
- [x] 5.15 Property test: freeze followed by thaw is the identity, eigenvariable levels included

## 6. Conformance corpus (ELPI 1.18-defined behaviour)

- [x] 6.1 Add `tests/conformance/corpus/constraints/delay_resume.elpi`: suspend, resume order, and failure of a resumed goal
- [x] 6.2 Add `tests/conformance/corpus/constraints/backtrack_store.elpi`: constraints added and removed across choice points
- [x] 6.3 Add `tests/conformance/corpus/constraints/chr_simplify.elpi`, `chr_propagate.elpi` and `chr_guard.elpi`, including several blocks and simpagation
- [x] 6.4 Add `tests/conformance/corpus/constraints/chr_scoped.elpi`: constraints under `pi`/`=>`, and `(Ctx ?- C)` heads
- [x] 6.5 Add `tests/conformance/corpus/constraints/residual.elpi`: compare the residual constraint output textually with the oracle
- [x] 6.6 Add `tests/conformance/corpus/constraints/leq_cycle.elpi`, using the shipped `leq` solver
- [x] 6.7 Add `tests/conformance/corpus/constraints/stuck_unif.elpi`: problems outside the fragment are suspended and reported as residual, with no hooks
- [x] 6.8 Run the harness against `elpi` 1.18, and record any divergence that cannot be fixed in the known-divergence register with a reason

## 7. Knowledge graph and docs

- [x] 7.1 Update the [[changes#add-elpi-constraints]] section and the components [[components#Constraint store]] and [[components#CHR engine]] (with `introduced_by` and `depends_on` edges) to match the implementation
- [x] 7.2 Add `openspec: [elpi-constraints, elpi-solver-api]` to the frontmatter of `tg.md/papers/solvers.md` and `tg.md/architecture/components.md`, and name the requirements in prose (for example `elpi-constraints › CHR rules`)
- [x] 7.3 Update [[uml#Machine state diagram]] with the wake-queue drain state
- [x] 7.4 Update [[solvers]] with worked T1/T3/T4 examples that match the scenarios

## 8. Verification

- [x] 8.1 Run `openspec validate add-elpi-constraints --strict`
- [x] 8.2 Run `tg check` and fix every broken link, code ref and annotation
- [x] 8.3 Run `tg trace elpi-constraints elpi-solver-api --gaps` and close every unimplemented or unverified requirement and scenario it reports
