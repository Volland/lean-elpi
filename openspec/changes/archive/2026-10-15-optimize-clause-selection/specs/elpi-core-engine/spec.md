## MODIFIED Requirements

### Requirement: First-argument indexing
The engine SHALL index the clauses of every predicate on the head symbol of their first argument (constant, integer, string, list constructor or "variable"), and SHALL select candidate clauses for a call by the head symbol of the call's first argument when it is rigid. Clauses whose first argument has a different rigid head symbol SHALL be skipped without being tried and without creating a choice point. The candidate list for each key SHALL be prepared when clauses are added, so that selecting candidates for a call does no work proportional to the number of clauses. Indexing SHALL NOT change the set or order of answers.

#### Scenario: Clauses with a non-matching first argument are skipped
- **WHEN** the program is `p a 1.  p b 2.  p c 3.` and the query `p b X` is solved
- **THEN** it succeeds with `X = 2` and the machine reports no remaining choice point after the answer
- **AND** requesting a further solution fails immediately without trying the clauses for `a` or `c`

#### Scenario: Variable-headed clauses keep their place among keyed ones
- **WHEN** the program is `p "a" 1.  p X 2.  p "b" 3.  p "a" 4.` and all answers of `p "a" N` are requested
- **THEN** the answers are `N = 1`, `N = 2`, `N = 4`, in that order
- **AND** `p "c" N` has the single answer `N = 2`

### Requirement: Hypothesis indexing
A hypothetical clause added with `=>` SHALL be selected for a goal by its head predicate and by the first argument: a goal whose first argument is an eigenvariable SHALL NOT be tried against a hypothesis whose first argument is a different eigenvariable or a constant, while a variable or a λ in either position SHALL remain a possible match. A call SHALL NOT examine hypotheses about other predicates. Selection SHALL NOT change which clauses can apply, only how many are attempted.

#### Scenario: A goal picks the hypothesis about its own name
- **WHEN** 300 nested `pi x\ p x N => …` scopes are opened and the innermost goal is `p x 300`
- **THEN** the goal succeeds using the innermost hypothesis

#### Scenario: Hypotheses about other predicates are not consulted
- **WHEN** 2000 hypotheses `q i` are in scope and the goal `count 50000` (a static predicate) runs inside them
- **THEN** it succeeds in time independent of the number of `q` hypotheses

## ADDED Requirements

### Requirement: Compiled clauses and term sharing
The engine SHALL compile a clause when it is added to the program: its head arguments SHALL be kept as an array and its body as a sequence of goals, with top-level conjunctions split and `true` removed, every goal carrying the cut barrier of the call. Instantiating a clause and normalising a term SHALL return every subterm that does not change as the same value rather than a copy, and dereferencing a variable bound to a λ-term SHALL relocate and β-reduce it in one traversal. Neither SHALL change answers, their order or the effect of cut.

#### Scenario: Cut in a compiled body
- **WHEN** the program is `p 1.  p 2.  r X :- p X, !, X > 0.  r 3.` and all answers of `r X` are requested
- **THEN** the only answer is `X = 1`, as with the oracle

#### Scenario: Instantiating a clause body keeps its ground parts
- **WHEN** a clause body `f X (g 1 (h "x"))` is instantiated at depth 0 with `X := 7`
- **THEN** the argument `g 1 (h "x")` of the result is the very same value as in the stored clause, not a copy
- **AND** instantiating or normalising a term without clause variables or assigned variables returns the term itself
