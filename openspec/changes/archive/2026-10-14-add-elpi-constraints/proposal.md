## Why

Milestone **M2** of LeanElpi. After `add-elpi-core` (M1) the engine runs plain λProlog, but real ELPI programs (Coq-Elpi's type checkers, elaborators and user solvers) rely on delayed goals and Constraint Handling Rules. Without them we cannot match the ELPI 1.18 oracle on that corpus, and users cannot write their own solvers, which is project goal 3. The Solver API also needs its two remaining tiers, native constraint handlers (T3) and unification hooks (T4), before M3 exposes the engine to Lean.

**Depends on:** `add-elpi-core` (M1): term store, unifier, persistent substitution, abstract machine, solver registry and the T2 builtin tier.

## What Changes

- Add delayed goals: `declare_constraint Goal [Vars]` suspends `Goal` on a list of keys and resumes it as soon as one of them is assigned. Unification problems outside the pattern fragment use the same mechanism.
- Add a constraint store that lives inside the persistent machine state. A choice point captures it, so backtracking drops every constraint added after that choice point and brings back every constraint removed after it.
- Add CHR rules in ELPI 1.18 syntax: `constraint p q { rule (Kept) \ (Removed) | (Guard) <=> (Body). }`. They cover simplification (constraints after `\` are removed), propagation (no `\`, everything is kept) and simpagation. Rule heads match against the store, the guard cannot bind variables of the matched constraints, and the body runs as a new goal.
- Add scoped constraints. A constraint declared under `pi`/`=>` records its eigenvariables and local program, and CHR heads of the form `(Ctx ?- Goal)` respect that scope.
- Report residual constraints: constraints still in the store when a query succeeds come back with the answer, in the oracle's format on the CLI and as data in the Lean API.
- Solver API tier T1: CHR solvers written in ELPI, packaged as libraries (for example the `leq` partial-order solver with cycle detection).
- Solver API tier T3: native constraint handlers registered with `@[elpi_constraint_handler "name"] def h : ConstraintHandler`. A handler declares its `keys` and provides `onAdd`/`onWake`, each returning a `HandlerResult` (simplify, propagate goals, fail, keep). Its state lives in the backtrackable store.
- Solver API tier T4: unification hooks registered with `@[elpi_unif_hook]`. A hook is consulted only when pattern unification is stuck and may solve, suspend or fail. It never overrides a syntactic success.

## Capabilities

### New Capabilities
- `elpi-constraints`: delayed goals, the backtrackable constraint store, CHR rules, scoped constraints and residual constraint reporting, matching ELPI 1.18.

### Modified Capabilities
- `elpi-solver-api`: adds the T1 (CHR solvers in ELPI), T3 (native constraint handlers) and T4 (unification hooks) tiers to the API introduced by `add-elpi-core`. These are ADDED requirements, and no existing requirement changes.

## Impact

**Motivating decisions:**
- [[decisions#Tiered solver API]]: T1, T3 and T4 are delivered here (T2 shipped in M1).
- [[decisions#Staged language surface]]: constraints and CHR form stage M2.
- [[decisions#Persistent store]]: the constraint store and handler state live in the persistent state and backtrack for free.
- [[decisions#Explicit abstract machine]]: the wake-up queue and CHR firing are machine transitions, not host recursion.
- [[decisions#ELPI 1.18 dialect]]: `declare_constraint`, `constraint … { rule … }` and residual printing follow 1.18 syntax and semantics.
- [[decisions#Specs before code]]

**Constraints:**
- [[constraints#Oracle is ELPI 1.18]]: CHR firing order and residual output are checked against the oracle.
- [[constraints#Pattern unification is decidable]] and [[constraints#CIC unification is undecidable]]: problems outside the fragment are suspended rather than solved, and T4 hooks are the only way to extend unification.
- [[constraints#Upstream ELPI is LGPL]]: the CHR engine is written clean-room from the published semantics.

**Components introduced:**
- [[components#Constraint store]] (`Elpi/Core/Constraints.lean`)
- [[components#CHR engine]] (`Elpi/Core/CHR.lean`)
- Extended: [[components#Abstract machine]] (wake-up queue), [[components#Unifier]] (stuck problems → suspension / hooks), [[components#Solver registry]] (handler and hook attributes), [[components#Standard library]] (T1 solver libraries).

**Concepts:** [[glossary#Delayed goal]], [[glossary#Constraint Handling Rules]], [[glossary#Constraint handler]], [[glossary#Unification hook]], [[glossary#Eigenvariable]].

**Knowledge graph sections touched:** [[changes#add-elpi-constraints]], [[solvers]], [[uml#Machine state diagram]].

**Requirements added:**
- [[openspec:elpi-constraints#Delayed goals]]
- [[openspec:elpi-constraints#Backtrackable constraint store]]
- [[openspec:elpi-constraints#CHR rules]]
- [[openspec:elpi-constraints#Scoped constraints]]
- [[openspec:elpi-constraints#Residual constraints]]
- [[openspec:elpi-solver-api#CHR solvers in ELPI]]
- [[openspec:elpi-solver-api#Native constraint handlers]]
- [[openspec:elpi-solver-api#Unification hooks]]

**APIs:** new Lean types `ConstraintHandler`, `HandlerResult`, `UnifHook` and the attributes `@[elpi_constraint_handler]` and `@[elpi_unif_hook]`. `Solution` gains a `constraints` field. Nothing breaks for M1 programs that never suspend a goal.
