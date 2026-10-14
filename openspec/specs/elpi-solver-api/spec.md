# elpi-solver-api Specification

## Purpose
The extension API through which users add their own solvers to the engine. This change delivers tier T2, Lean-implemented builtin predicates registered by attribute; the CHR, native-handler and unification-hook tiers follow in `add-elpi-constraints`.

## Requirements

### Requirement: Lean builtin predicates
Users SHALL be able to implement an ELPI predicate as a Lean function and declare it with `@[elpi_builtin "name" "pred name m1:T1, ..., mn:Tn."]`. The signature string SHALL be parsed and typechecked when the attribute is applied, and every call to the builtin in an ELPI program SHALL be typechecked against it at load time. The implementation SHALL receive the call's arguments with input arguments dereferenced, and SHALL return a lazy stream of solutions, each solution being a set of bindings for the output arguments; an empty stream SHALL mean failure, and each further element SHALL be an alternative explored on backtracking. The implementation SHALL run in the engine's host monad, so that its effects are captured by choice points and rolled back on backtracking.

#### Scenario: Builtin signature is typechecked
- **WHEN** a builtin is declared with `@[elpi_builtin "succ" "pred succ i:int, o:int."]` and a program contains the clause `q X :- succ "a" X.`
- **THEN** loading the program fails with a type error at the argument `"a"`
- **AND** applying the attribute with the malformed signature `"pred succ i:int o:"` fails at elaboration time with a parse error

#### Scenario: Builtin returns a stream of solutions
- **WHEN** a builtin `between` with signature `pred between i:int, i:int, o:int.` returns the stream of integers from its first to its second argument, and the query `between 1 3 X` is solved for all solutions
- **THEN** the solutions are `X = 1`, `X = 2`, `X = 3` in that order
- **AND** when only the first solution is demanded, the builtin's stream is forced only once

#### Scenario: Builtin runs in the host monad
- **WHEN** a builtin implemented in `MetaM` creates a fresh Lean metavariable and the engine runs the query `(mk-mvar, fail) ; true` under the `MetaM` instance
- **THEN** the query succeeds and the metavariable context after the query does not contain the metavariable created in the failed branch

### Requirement: Attribute registration
Builtins declared with `@[elpi_builtin]` SHALL be recorded in a persistent Lean environment extension, so that they are available in every module that imports the declaring module, without any explicit registration call. Programs loaded or compiled in an environment SHALL see exactly the builtins registered in that environment, and registering two builtins with the same name SHALL be reported as an error at the second registration.

#### Scenario: Solver from an imported module is available
- **WHEN** module `A` declares `@[elpi_builtin "double" "pred double i:int, o:int."]` and module `B` imports `A` and loads a program whose query is `double 21 X`
- **THEN** the query succeeds with `X = 42` without any registration code in `B`

### Requirement: CHR solvers in ELPI
The Solver API SHALL support tier T1: a solver written entirely in ELPI, as predicates that suspend with `declare_constraint` plus one or more `constraint … { rule … }` blocks. It is loaded with `accumulate` like any other ELPI file. A T1 solver SHALL need no Lean code and SHALL behave the same in every embedding (Lean commands and tactics, the runtime library, the CLI), with answers and residual constraints identical to the ELPI 1.18 oracle on the same source. Several T1 solvers accumulated into one program SHALL coexist, and each one's rules see only the constraints of the predicates listed in its own `constraint` header.

#### Scenario: leq solver detects a cycle
- **WHEN** a program accumulates a `leq` solver with reflexivity (`rule \ (leq X X).`), antisymmetry (`rule (leq X Y) \ (leq Y X) <=> (X = Y).`), idempotence and transitivity rules, and runs the query `leq A B, leq B C, leq C A`
- **THEN** the cycle collapses: `A`, `B` and `C` are unified, and the query succeeds with no residual `leq` constraints
- **AND** the answer and the (empty) residual output match the oracle's for the same program

### Requirement: Native constraint handlers
The Solver API SHALL support tier T3: native constraint handlers declared in Lean as `@[elpi_constraint_handler "name"] def h : ConstraintHandler`. A handler SHALL declare `keys`, the ELPI predicate names it owns. Every constraint with such a predicate goes to the handler instead of the generic suspension and CHR path. The engine SHALL call `onAdd : Constraint → Store → HandlerResult` when a constraint the handler owns is added, and `onWake : UVar → Store → HandlerResult` when a variable one of its constraints is suspended on gets assigned. A `HandlerResult` SHALL be one of:
- simplify: replace the handler's constraints with a given set.
- propagate: keep the constraints and push the given goals.
- fail: start backtracking.
- keep: store the constraint unchanged.

Handler state SHALL live in the backtrackable constraint store, so it is restored on backtracking like every other constraint. A handler registered in an imported module SHALL be available without further setup, as for builtins.

#### Scenario: Handler simplifies a new constraint
- **WHEN** a handler `"lia"` with ``keys := [`lia.le]`` is registered and the query `declare_constraint (lia.le X 3) [X], declare_constraint (lia.le X 5) [X]` runs
- **THEN** `onAdd` receives `lia.le X 5` with `lia.le X 3` already in the store and returns simplify, keeping only the stronger bound
- **AND** the answer reports the single residual constraint `lia.le X 3`

#### Scenario: Handler wakes on variable instantiation
- **WHEN** the store holds `lia.le X 3`, owned by the `"lia"` handler, and the query then runs `X = 7`
- **THEN** the engine calls `onWake` with `X`, the handler returns fail, and the unification `X = 7` fails
- **AND** running `X = 2` instead makes `onWake` return simplify with an empty set, so no residual constraint remains

#### Scenario: Handler state backtracks with the store
- **WHEN** the query `(declare_constraint (lia.le X 3) [X], fail ; declare_constraint (lia.le X 5) [X])` runs against the `"lia"` handler
- **THEN** the call to `onAdd` in the second branch sees a store with no bound from the first branch
- **AND** the answer reports the residual constraint `lia.le X 5`

### Requirement: Unification hooks
The Solver API SHALL support tier T4: unification hooks declared in Lean as `@[elpi_unif_hook] def h : UnifHook`. The engine SHALL consult hooks only when pattern unification is stuck, that is, when a problem falls outside the pattern fragment or a rigid-rigid clash involves a symbol the hook declares as interpreted. A hook SHALL return one of:
- solved: a substitution, which the engine checks for scope and occurs violations before applying it.
- suspend: delay the problem as a goal keyed on its flexible variables.
- fail: start backtracking.

Hooks SHALL NOT be consulted for problems that pattern unification solves or rejects on its own, so they cannot change the answer of a syntactically decided problem. With no hook registered, stuck problems are suspended exactly as in ELPI 1.18.

#### Scenario: Hook is consulted only when unification is stuck
- **WHEN** a hook that counts its calls and returns suspend is registered, and the query `X = f a, F a = g a` runs, where `a` is a global constant
- **THEN** `X = f a` is solved without calling the hook, the hook is called exactly once for `F a = g a`, and that problem is reported as a residual constraint

#### Scenario: Hook cannot override syntactic success
- **WHEN** a hook that returns fail for every problem is registered, and the query `f X = f a` runs
- **THEN** the query succeeds with `X = a` and the hook is never called
