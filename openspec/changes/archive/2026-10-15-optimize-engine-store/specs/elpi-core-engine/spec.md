## MODIFIED Requirements

### Requirement: Persistent store
The binding of unification variables SHALL be held in a store that behaves as a value: a store that was passed to an operation SHALL be unchanged afterwards for any caller that kept it, and the operations that derive a new store SHALL NOT make the cost of a binding depend on the size of the store or of the terms involved. Every choice point SHALL capture both a checkpoint of the store and a snapshot of the host monad state, and backtracking to a choice point SHALL restore both exactly, discarding every binding and every host-state change made after it was created.

#### Scenario: Backtracking restores the substitution
- **WHEN** the query `(X = 1, Y = a, fail) ; Z = X` is solved
- **THEN** it succeeds with `Z = X` and with `X` and `Y` unassigned, because the bindings made in the first branch are discarded on backtracking

#### Scenario: Choice point restores host monad state
- **WHEN** the engine runs in a host monad with a counter, a builtin `incr` increments the counter, and the query `(incr, fail) ; read-counter N` is solved starting from counter value 0
- **THEN** it succeeds with `N = 0`, because the counter increment made in the failed branch is rolled back when the choice point is restored

#### Scenario: Binding a variable does not copy the term it is bound to
- **WHEN** `append` of two lists is run for lists of 81920 elements each
- **THEN** it succeeds in time and memory proportional to the length of the lists
- **AND** no step walks or copies the tail of the list that a clause variable is bound to

#### Scenario: Backtracking in a large store
- **WHEN** a query creates 100000 variables and then backtracks through 2000 alternatives
- **THEN** each alternative starts from exactly the bindings it had when its choice point was created

## ADDED Requirements

### Requirement: Hypothesis indexing
A hypothetical clause added with `=>` SHALL be selected for a goal by its head predicate and by the first argument: a goal whose first argument is an eigenvariable SHALL NOT be tried against a hypothesis whose first argument is a different eigenvariable or a constant, while a variable or a λ in either position SHALL remain a possible match. Selection SHALL NOT change which clauses can apply, only how many are attempted.

#### Scenario: A goal picks the hypothesis about its own name
- **WHEN** 300 nested `pi x\ p x N => …` scopes are opened and the innermost goal is `p x 300`
- **THEN** the goal succeeds using the innermost hypothesis
