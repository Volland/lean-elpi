## Purpose
The stable Lean surface for programs that embed LeanElpi as a library: predicate signatures, goals built from terms, structured solution terms, resumable fuel slices, bulk facts as terms, multi-unit loading and a public clause AST, behind one `Elpi.Host` module.

## ADDED Requirements

### Requirement: Predicate signature lookup
LeanElpi SHALL provide a pure Lean function that, given a compiled program and a predicate name, returns the predicate's declared argument types as structured type terms (kind constants, type applications, arrows, type variables) and the mode of each argument (`i` or `o`), or nothing when the predicate is not declared. Arguments declared with `type` rather than `pred` SHALL report mode `o`, as the ELPI loader defaults them. Comparing two type terms with `==` agrees with equality; this is proved (`TyTerm.beq_iff_eq`).

#### Scenario: Declared predicate
- **WHEN** a program declaring `pred violation i:dept, o:person, o:string.` is compiled and `violation` is looked up
- **THEN** the result lists three arguments with types `dept`, `person`, `string` and modes `i`, `o`, `o`

#### Scenario: Polymorphic predicate
- **WHEN** `pred closure i:(A -> A -> prop), i:A, o:A.` is looked up
- **THEN** the first argument's type is an arrow over the type variable `A`, reported as a variable, not instantiated

#### Scenario: Unknown predicate
- **WHEN** a name with no declaration is looked up
- **THEN** the function returns nothing and raises no error

### Requirement: Goals built from terms
LeanElpi SHALL let a caller build a query goal from a predicate name and a list of argument terms (constants, applications, integer, float and string literals, lists, and fresh output variables) without printing and re-parsing text. The goal SHALL be type-checked against the predicate's signature before solving, and a type mismatch SHALL be an error naming the argument position.

#### Scenario: Input values are not parsed as source
- **WHEN** a goal is built for `name_of i:string, o:person` with the string argument `"x\" , evil Y"`
- **THEN** the engine receives one string literal equal to that text
- **AND** no extra goal or variable appears

#### Scenario: Ill-typed argument
- **WHEN** a goal passes an integer where the signature declares `person`
- **THEN** building or checking the goal fails with an error naming argument 1

### Requirement: Structured solution terms
LeanElpi SHALL return each solution's bindings for the requested output variables as values of a Lean inductive type of result terms: constants, applications with an argument array, integer, float and string literals, lists, and markers for an unbound variable, a λ-abstraction, and opaque host data. It SHALL also provide a JSON encoding of that type for the C interface; decoding an encoded term gives it back, which is proved (`ResultTerm.json_roundtrip`). Floats are carried as their IEEE-754 bits so the round trip is exact. Suspended constraints SHALL be reported alongside, as today.

#### Scenario: Constructor application
- **WHEN** a query binds `P` to `person 42`
- **THEN** the binding is the application of constant `person` to the integer literal `42`

#### Scenario: Unbound output
- **WHEN** a solution leaves an output variable unbound
- **THEN** the binding is the unbound-variable marker, not a printed variable name

#### Scenario: JSON form round-trips
- **WHEN** any result term is encoded to `Lean.Json` and decoded back
- **THEN** the decoded term equals the original

### Requirement: Resumable fuel slices
LeanElpi SHALL let a caller run a prepared query for at most N resolution steps and receive one of: a solution together with a machine that resumes the search, exhaustion, an error, or a paused machine when the N steps ran out. Resuming a paused machine with more fuel SHALL continue the same search. Running a query in slices of any size SHALL yield the same solutions, in the same order, as running it with one budget equal to the sum of the slices. Pausing SHALL keep the single-owner discipline of the store, so in-place updates are not turned into copies. A nested `findall` runs to completion inside the slice that starts it, so that one slice may run longer than N steps; solutions and the point where the whole budget runs out are unaffected.

#### Scenario: Slices equal one run
- **WHEN** a query whose full search takes about 10⁶ steps is run once with ample fuel, and again in slices of 1000 steps, resuming after each pause
- **THEN** both runs produce the same solution sequence and the same exhaustion result

#### Scenario: Pausing does not copy the store
- **WHEN** the scaling test runs a long query in slices of 1000 steps
- **THEN** its run time stays within 10% of the single-run time, as `tests/Core/Scaling.lean` measures

### Requirement: Public clause AST
LeanElpi SHALL expose, as a stable public Lean API, the parsed and type-checked form of a program: its `kind`, `type` and `pred` declarations with modes, its `accumulate` directives, and each clause's head and body with source positions. Body goals SHALL distinguish conjunction, disjunction, negation (`not`; ELPI 1.18 has no `\+`), cut, `pi`, `sigma`, implication (`=>` and `<=`, whose hypothetical clauses may use `:-`), predicate calls with the called name, and builtin calls.

#### Scenario: Negation and cut are visible
- **WHEN** the clause `v P :- person.name P _, !, not (reports_to P _ _).` is inspected
- **THEN** its body is a conjunction of a call to `person.name`, a cut, and a negation whose inner goal calls `reports_to`

#### Scenario: Hypothetical clause is visible
- **WHEN** the goal `(reports_to X E Y :- true) => check X` appears in a clause body
- **THEN** it is reported as an implication whose hypothetical clause has head predicate `reports_to`

### Requirement: Bulk fact loading
LeanElpi SHALL let a caller add ground facts to a compiled program as terms, without printing and parsing, in batches of any size, producing a new program value and leaving the original valid. Each fact SHALL be checked against its predicate's signature. Loading N facts into a predicate SHALL cost time linear in N plus the predicate's existing clauses, and first-argument indexing SHALL apply to the loaded facts as it does to parsed clauses. A batch is all or nothing; this is proved (`addFacts_atomic`).

#### Scenario: Facts from terms answer queries
- **WHEN** 100 000 facts `person.name (person K) "nK"` are added as terms and `person.name (person 77) N` is solved
- **THEN** the single solution binds `N` to `"n77"`

#### Scenario: Loading is linear
- **WHEN** 10⁵ and then 10⁶ facts are added
- **THEN** the second load takes at most 15 times as long as the first

#### Scenario: Ill-typed fact is rejected
- **WHEN** a fact `person.name "x" 1` is added against `pred person.name o:person, o:string.`
- **THEN** the batch fails with an error naming the predicate and argument position, and no fact from the batch is added

### Requirement: Multi-unit load keeps positions
LeanElpi SHALL compile a program from an ordered list of named source units, such as a generated signature followed by a module's source, as one program. Type and parse errors SHALL report the unit name and the line and column within that unit, lines counting from 1 and columns from 0 as in Lean positions.

#### Scenario: Error position inside the module
- **WHEN** the units `signature` (200 lines) and `org-rules` are compiled and `org-rules` has a type error on line 3, column 10
- **THEN** the error reports unit `org-rules`, line 3, column 10
