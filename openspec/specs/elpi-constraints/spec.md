# elpi-constraints Specification

## Purpose
Delayed goals and Constraint Handling Rules for the LeanElpi engine, matching the ELPI 1.18 semantics. Goals suspend on unassigned variables, live in a backtrackable store, are rewritten by CHR rules, respect `pi` scopes, and are reported as residual constraints when unsolved.

## Requirements

### Requirement: Delayed goals
The engine SHALL implement the ELPI 1.18 builtin `declare_constraint Goal Keys`. It suspends `Goal` and indexes it on every unification variable that occurs as a key (or as the head of a key) in the list `Keys`. When any one of those keys is assigned, the engine SHALL resume the suspended goal before it runs the next goal of the current conjunction, and resumed goals run in the order they were woken. A resumed goal SHALL behave like an ordinary call: its failure makes the triggering unification fail and starts backtracking. Unification problems outside the pattern fragment SHALL be suspended through the same mechanism, keyed on the flexible heads involved. On each of these points the ELPI 1.18 oracle's answer is the reference.

#### Scenario: Goal suspends on an unassigned variable
- **WHEN** the program `pred even i:int. even N :- 0 is N mod 2.` runs the query `declare_constraint (even X) [X], print "after"`
- **THEN** the query succeeds and prints `after` without running any clause of `even`
- **AND** the store holds one suspended goal `even X` keyed on `X`

#### Scenario: Suspended goal resumes on assignment
- **WHEN** the same program runs `declare_constraint (even X) [X], X = 4, print "done"`
- **THEN** `even 4` runs right after `X = 4` and before `print "done"`, and the query succeeds with `X = 4` and no suspended goals
- **AND** the query `declare_constraint (even X) [X], X = 3` fails, because the resumed goal `even 3` fails

### Requirement: Backtrackable constraint store
The constraint store SHALL be part of the persistent machine state, so every choice point captures it. When the engine backtracks to a choice point, the store SHALL be exactly what it was when that choice point was created: constraints added after it are gone, constraints removed after it are back, and native handler state is rolled back the same way. Backtracking SHALL NOT run any compensating code to restore the store.

#### Scenario: Backtracking removes constraints added later
- **WHEN** the query `(declare_constraint (p X) [X], fail ; true)` runs
- **THEN** the query succeeds through the second branch with no suspended goal `p X` in the store or the answer
- **AND** the query `declare_constraint (q X) [X], (X = 1, fail ; true)` succeeds with `q X` still suspended and `X` unassigned, because waking it in the failed branch has been undone

### Requirement: CHR rules
The engine SHALL accept ELPI 1.18 constraint blocks `constraint P1 … Pn { rule … }`, whose rules have the form `rule (K1) … (Ki) \ (R1) … (Rj) | (Guard) <=> (Body)`. The `\`, `|` and `<=>` parts are each optional. Constraints `K` to the left of `\` SHALL be kept and constraints `R` to the right SHALL be removed. With no `\`, every head is kept (propagation); with nothing to the left of `\`, every head is removed (simplification). Heads SHALL be matched against store constraints whose predicate is one of `P1 … Pn`, and unification variables in the store are treated as frozen during matching and while the guard runs, so a guard that would assign one of them fails. A rule SHALL be tried whenever a constraint is added to the store, with that new constraint among the heads. When the guard succeeds, the `R` constraints are removed and then `Body` runs as a new goal. Which rules fire, in what order and on which partners SHALL match the ELPI 1.18 oracle.

#### Scenario: Simplification rule replaces constraints
- **WHEN** the program declares `constraint leq { rule \ (leq X Y) (leq Y X) <=> (X = Y). }` and `leq A B :- declare_constraint (leq A B) [A,B].`, and runs the query `leq P Q, leq Q P`
- **THEN** both `leq` constraints are removed from the store and `P = Q` runs
- **AND** the query succeeds with `P` and `Q` unified and no residual constraints

#### Scenario: Propagation rule adds constraints
- **WHEN** the block is `constraint leq { rule (leq X Y) \ (leq X Y). rule (leq X Y) (leq Y Z) <=> (leq X Z). }` and the query is `leq A B, leq B C`
- **THEN** the store ends up with exactly `leq A B`, `leq B C` and `leq A C`, and the kept heads are not duplicated

#### Scenario: Failing guard prevents firing
- **WHEN** the block is `constraint pos { rule \ (pos X N) | (N > 0) <=> true. }` and the query is `declare_constraint (pos X 0) [X]`
- **THEN** the rule does not fire, `pos X 0` stays in the store, and the query still succeeds
- **AND** with the guard `| (X = 1)` the rule does not fire either, because the guard may not assign the frozen variable `X`

### Requirement: Scoped constraints
A goal suspended under `pi` and `=>` SHALL record its context: the eigenvariables in scope and the local clauses added by `=>`. When it resumes, the goal SHALL run in that recorded context, even if the resumption happens after control has left the `pi`. CHR heads written as `(Ctx ?- C)` SHALL bind `Ctx` to the recorded context of the matched constraint. A rule SHALL NOT make a variable from outside a scope stand for one of that scope's eigenvariables: a unification that would do so fails, as in core unification. The ELPI 1.18 oracle's answers are the reference.

#### Scenario: Constraint under pi respects eigenvariables
- **WHEN** the query `pi c\ (mem c => declare_constraint (chk c X) [X]), X = 1` runs, where `chk C N :- mem C.`
- **THEN** `chk c 1` resumes after `X = 1` with the local clause `mem c` visible, and the query succeeds
- **AND** the query `pi c\ (declare_constraint (chk c X) [X], X = c)` fails, because `X` was created outside the scope of `c`
- **AND** the rule `rule (G ?- chk C N) <=> (print G)` prints the context recorded for the constraint, which includes `mem c`

### Requirement: Residual constraints
When a query succeeds while suspended goals or CHR constraints remain in the store, the engine SHALL return them together with that answer. Each residual constraint SHALL be shown with the answer substitution applied, its recorded context and the variables it is suspended on. The CLI SHALL print residual constraints after the answer substitution in the ELPI 1.18 oracle's format, and the conformance harness compares that output. The Lean runtime API SHALL expose them as a list of constraints on each solution value.

#### Scenario: Unsolved constraints are reported with the answer
- **WHEN** the CLI runs the query `declare_constraint (even X) [X], Y = 2`
- **THEN** it prints the answer `Y = 2` and then the residual constraint `even X` suspended on `X`, matching the oracle's output for the same program
- **AND** the solution returned by the Lean runtime API carries exactly one residual constraint
