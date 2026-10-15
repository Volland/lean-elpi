# elpi-core-engine Specification

## Purpose
The native Lean 4 engine that runs ELPI 1.18 programs: term representation, higher-order pattern unification, hereditary Harrop goal solving, control (cut, spilling, depth-first search), program structure (grafting, accumulate, namespaces, indexing) and core builtins, with the same answers in the same order as the upstream `elpi` 1.18 oracle.

## Requirements

### Requirement: Term representation
The engine SHALL represent λProlog terms as constants, bound variables, applications, λ-abstractions, unification variables, literals (integers, floats, strings) and opaque builtin data. Bound variables SHALL be encoded as de Bruijn levels, so that a term built under a binder can be reused under further binders without index shifting, and α-equivalent terms SHALL be structurally equal. Every unification variable SHALL record the scope level (the number of enclosing `pi` eigenvariables) at which it was created, and the engine SHALL never assign it a term that mentions an eigenvariable introduced at a deeper level.

#### Scenario: Bound variables use de Bruijn levels
- **WHEN** the parser reads the two terms `x\ y\ x` and `a\ b\ a`
- **THEN** both are represented by the same term value, with the body referring to the outer binder by level 0
- **AND** the two terms compare equal and have the same hash

#### Scenario: Unification variables carry their scope level
- **WHEN** the query `pi c\ X = c` is solved, where `X` is a query variable created at level 0
- **THEN** the query fails, because assigning `X := c` would let `X` mention the eigenvariable `c` introduced at level 1
- **AND** the oracle's answer (failure) is the reference

### Requirement: Higher-order pattern unification
The engine SHALL unify terms modulo α-, β- and η-conversion and SHALL compute most general unifiers for every problem in Miller's pattern fragment, that is, problems where each unification variable is applied to distinct bound variables or eigenvariables that are in scope. Solving SHALL use inversion of the distinct-variable spine and pruning of arguments that cannot occur, and SHALL perform an occurs check so that no variable is assigned a term containing itself. A problem outside the pattern fragment SHALL NOT fail and SHALL NOT be solved by guessing; it SHALL be suspended as a delayed goal and re-examined once its head variable is assigned, and any problem still suspended when a solution is reached SHALL be reported with that solution as residual. Where ELPI 1.18 defines the answer, the oracle's answer is the reference.

#### Scenario: Pattern problem has a most general unifier
- **WHEN** the query `pi a\ pi b\ X a b = f b a` is solved
- **THEN** it succeeds exactly once with `X = x\ y\ f y x` (up to α-renaming)
- **AND** the oracle prints the same answer

#### Scenario: Occurs check rejects cyclic solution
- **WHEN** the query `X = f X` is solved
- **THEN** the query fails and no assignment of `X` is produced

#### Scenario: Problem outside the pattern fragment is suspended
- **WHEN** the query `pi a\ (X a a = f a, X = x\ y\ f y)` is solved, whose first conjunct applies `X` to a repeated argument
- **THEN** the first conjunct is suspended instead of failing, and after `X` is assigned by the second conjunct the suspended problem is re-checked and the query succeeds with `X = x\ y\ f y`
- **AND** solving `pi a\ X a a = f a` alone succeeds with the suspended problem reported as a residual delayed goal rather than an assignment of `X`

### Requirement: Hereditary Harrop goals
The engine SHALL solve goals of first-order hereditary Harrop formulas extended with λ-terms: `true`, conjunction `,` (and `&`), disjunction `;`, universal quantification `pi x\ G`, implication `D => G`, existential `sigma x\ G`, and atomic goals. Solving `pi x\ G` SHALL introduce a fresh eigenvariable at the next scope level, distinct from every other constant. Solving `D => G` SHALL make the clauses of `D` available only while solving `G` and SHALL remove them when `G` finishes or is backtracked over. Solving `G1 ; G2` SHALL try `G1` first and SHALL try `G2` only on backtracking.

#### Scenario: Universal goal introduces a fresh constant
- **WHEN** the queries `pi x\ x = x` and `pi x\ pi y\ x = y` are solved
- **THEN** the first succeeds and the second fails, because `x` and `y` are distinct eigenvariables

#### Scenario: Implication extends the program locally
- **WHEN** the program declares `pred q o:int.` with no clauses and the query `(q 1 => q X)` is solved
- **THEN** it succeeds with `X = 1`
- **AND** a subsequent query `q Y` against the same program fails, because the hypothetical clause is no longer in scope

#### Scenario: Disjunction backtracks into the second branch
- **WHEN** the query `(X = 1 ; X = 2), X > 1` is solved
- **THEN** the first branch binds `X = 1`, the test `X > 1` fails, the engine backtracks into the second branch, and the query succeeds with `X = 2`

### Requirement: Cut
The engine SHALL implement the cut `!` with the ELPI 1.18 semantics: executing `!` in the body of a clause SHALL discard every choice point created since the call that selected that clause, including the alternative clauses of the same predicate and the choice points of goals to its left in the body. A cut SHALL be local to the predicate call whose clause contains it and SHALL NOT remove choice points of the caller. Where ELPI 1.18 defines the answer set, the oracle's answer is the reference.

#### Scenario: Cut prunes remaining clauses of the predicate
- **WHEN** the program is `p 1 :- !.  p 2.` and the query `p X` is solved for all solutions
- **THEN** exactly one solution `X = 1` is produced

#### Scenario: Cut inside a called predicate does not escape it
- **WHEN** the program is `p 1 :- !.  p 2.  q X :- p X.  q 3.` and the query `q X` is solved for all solutions
- **THEN** the solutions are `X = 1` followed by `X = 3`, because the cut in `p` does not prune the second clause of `q`

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

### Requirement: Abstract machine
The engine SHALL execute programs on an explicit abstract machine whose goal stack, choice-point stack and cut barriers are heap data, so that the depth of ELPI recursion is not bounded by the native call stack. Every run SHALL take a fuel budget counting resolution steps; when the fuel is exhausted the run SHALL stop with a distinguishable resource error, not with failure. Solutions SHALL be returned as a lazy stream: the machine SHALL compute the next solution only when it is demanded and SHALL resume from the saved choice points.

#### Scenario: Deep recursion does not overflow the native stack
- **WHEN** the program `count 0.  count N :- N > 0, M is N - 1, count M.` runs the query `count 1000000` with sufficient fuel
- **THEN** the query succeeds without a stack overflow

#### Scenario: Fuel exhaustion reports a resource error
- **WHEN** the program `loop :- loop.` runs the query `loop` with a fuel budget of 10000 steps
- **THEN** the run ends with an out-of-fuel resource error after 10000 steps
- **AND** the error is distinguishable from an ordinary query failure

#### Scenario: Solutions are produced lazily
- **WHEN** the program `nat z.  nat (s N) :- nat N.` runs the query `nat X` and the caller takes the first three solutions of the stream
- **THEN** the caller receives `X = z`, `X = s z`, `X = s (s z)` and the computation terminates, although the predicate has infinitely many solutions

### Requirement: Depth-first search order
The engine SHALL use the fixed ELPI search strategy: goals are solved left to right, clauses of a predicate are tried in program order (after grafting and accumulation have fixed that order), and the search is depth-first with chronological backtracking. The sequence of answers of any query SHALL be identical, including order and multiplicity, to the sequence produced by the ELPI 1.18 oracle, which is the reference.

#### Scenario: Answers follow clause order
- **WHEN** the program is `p 1.  p 2.  p 3.  q X :- p X.  q 0.` and the query `q X` is solved for all solutions
- **THEN** the solutions are `X = 1`, `X = 2`, `X = 3`, `X = 0` in that order, matching the oracle

### Requirement: Spilling
The engine SHALL support spilling: a subterm `{G}` occurring inside an atomic goal or term, where `G` is a predicate call missing its last argument, SHALL be replaced by a fresh variable `V` and the call `G V` SHALL be solved immediately before the enclosing goal, in left-to-right order of the spilled subterms. The fresh variable SHALL be created at the scope level of the enclosing goal.

#### Scenario: Spilled call is solved before the enclosing goal
- **WHEN** the program is `pred succ i:int, o:int.  succ X Y :- Y is X + 1.` and the query `print {succ 1}` is solved
- **THEN** the engine first solves `succ 1 V` binding `V = 2`, then solves `print 2`, and the output is `2`

### Requirement: Clause names and grafting
The engine SHALL accept clause attributes `:name "n"`, `:before "n"` and `:after "n"`. A clause with `:name "n"` SHALL be registered under the name `n`; a clause with `:before "n"` (respectively `:after "n"`) SHALL be inserted into its predicate immediately before (respectively after) the clause named `n`, regardless of the file or accumulated unit in which it appears. A grafting attribute that names an unknown clause, or a duplicate `:name`, SHALL be reported as a load-time error. The resulting clause order is the order used by the search and SHALL match the oracle.

#### Scenario: Clause grafted before a named clause
- **WHEN** the program is `:name "base" r 1.  :before "base" r 0.` and the query `r X` is solved for all solutions
- **THEN** the solutions are `X = 0` followed by `X = 1`

#### Scenario: Clause grafted after a named clause
- **WHEN** the program is `:name "base" r 1.  r 3.  :after "base" r 2.` and the query `r X` is solved for all solutions
- **THEN** the solutions are `X = 1`, `X = 2`, `X = 3` in that order

### Requirement: Accumulate and namespaces
The loader SHALL support `accumulate f.` (and `accumulate "f".`), which includes the clauses and declarations of the unit `f.elpi` at that point of the program, resolved through the library search path. A unit SHALL be loaded at most once per program even when it is accumulated several times, directly or transitively. The loader SHALL support `namespace n { ... }`, which prefixes every constant declared or defined inside the block with `n.`; inside the block, a short name SHALL resolve to the namespaced constant when one exists and to the global constant otherwise.

#### Scenario: Accumulated file is loaded once
- **WHEN** `main.elpi` accumulates `a` and `lib`, `a.elpi` also accumulates `lib`, and `lib.elpi` contains `l 1.`
- **THEN** the query `l X` against `main.elpi` produces the single solution `X = 1`, not two copies

#### Scenario: Namespace qualifies predicate names
- **WHEN** the program is `namespace foo { pred bar o:int.  bar 1.  pred baz o:int.  baz X :- bar X. }`
- **THEN** the query `foo.baz X` succeeds with `X = 1`, the short name `bar` inside the block resolving to `foo.bar`
- **AND** the query `bar X` outside the namespace is reported as using an undeclared constant

### Requirement: First-argument indexing
The engine SHALL index the clauses of every predicate on the head symbol of their first argument (constant, integer, string, list constructor or "variable"), and SHALL select candidate clauses for a call by the head symbol of the call's first argument when it is rigid. Clauses whose first argument has a different rigid head symbol SHALL be skipped without being tried and without creating a choice point. Indexing SHALL NOT change the set or order of answers.

#### Scenario: Clauses with a non-matching first argument are skipped
- **WHEN** the program is `p a 1.  p b 2.  p c 3.` and the query `p b X` is solved
- **THEN** it succeeds with `X = 2` and the machine reports no remaining choice point after the answer
- **AND** requesting a further solution fails immediately without trying the clauses for `a` or `c`

### Requirement: Monad-generic engine
The engine core SHALL be parametric in a host monad `m` that provides `save : m σ` and `restore : σ → m Unit`, and SHALL NOT depend on `Lean.Meta`, `MetaM` or any elaborator state. The core SHALL ship an instance for a pure monad, so that queries run in ordinary Lean code, and the Lean integration SHALL provide an instance for `MetaM` whose `save`/`restore` capture and reinstate the full `Meta.SavedState`, including metavariable assignments, so that backtracking rewinds every Lean-side effect of a failed branch.

#### Scenario: Core runs without MetaM
- **WHEN** a Lean file imports only the engine core modules and evaluates the query `append [1] [2] L` against a program defining `append` in the pure instance
- **THEN** the query yields `L = [1, 2]` and the import closure of the core modules contains no `Lean.Meta` module

#### Scenario: MetaM instance rewinds metavariable assignments
- **WHEN** the engine runs in `MetaM`, a builtin assigns a Lean metavariable `?m := 0` in the first branch of `(assign-m, fail) ; check-m-unassigned`
- **THEN** after backtracking into the second branch `?m` is unassigned again and the query succeeds

### Requirement: Core builtins
The engine SHALL provide the ELPI 1.18 core builtins with the oracle's behaviour as reference, including at least: `is` with integer and float arithmetic (`+`, `-`, `*`, `/`, `div`, `mod`, `abs`, `min`, `max`, conversions) and string concatenation `^`; comparisons `<`, `>`, `=<`, `>=`, `==`; control `fail`, `not`, `true`; I/O `print`, `term_to_string` and `halt`; string functions `size`, `substring`, `int_to_string`, `string_to_int` (evaluated by `is`, as in the oracle) and the predicates `rex_match` and `rex.match`; and type tests `var`, `name`. Evaluating `is` on an expression containing an unassigned variable or ill-typed operands SHALL raise a runtime error, not fail silently.

#### Scenario: Arithmetic evaluation with is
- **WHEN** the queries `X is 2 + 3 * 4`, `Y is 7 div 2`, `Z is 7 mod 3` and `W is 2.0 * 1.5` are solved
- **THEN** they succeed with `X = 14`, `Y = 3`, `Z = 1` and `W = 3.0`, matching the oracle
- **AND** the query `V is U + 1` with `U` unassigned raises a runtime error

#### Scenario: Printing and string builtins
- **WHEN** the queries `print "a" 1`, `S is "foo" ^ "bar"` and `N is size "hello"` are solved
- **THEN** standard output receives the line `a 1`, and the answers are `S = "foobar"` and `N = 5`, matching the oracle

### Requirement: Hypothesis indexing
A hypothetical clause added with `=>` SHALL be selected for a goal by its head predicate and by the first argument: a goal whose first argument is an eigenvariable SHALL NOT be tried against a hypothesis whose first argument is a different eigenvariable or a constant, while a variable or a λ in either position SHALL remain a possible match. Selection SHALL NOT change which clauses can apply, only how many are attempted.

#### Scenario: A goal picks the hypothesis about its own name
- **WHEN** 300 nested `pi x\ p x N => …` scopes are opened and the innermost goal is `p x 300`
- **THEN** the goal succeeds using the innermost hypothesis
