## Purpose

The extension API through which users add their own solvers to the engine. This change delivers tier T2, Lean-implemented builtin predicates registered by attribute; the CHR, native-handler and unification-hook tiers follow in `add-elpi-constraints`.

## ADDED Requirements

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
