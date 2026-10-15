# elpi-typechecker Specification

## Purpose
The load-time static checker for ELPI 1.18 programs: `kind`, `type` and `pred` declarations, argument modes, prenex polymorphism and type abbreviations, rejecting ill-typed programs with positioned errors before any query runs.

## Requirements

### Requirement: Signature declarations
The loader SHALL accept `kind c type -> ... -> type.` declarations of type constructors, `type c T.` declarations of constants (including several comma-separated names sharing one type), and `pred p m1:T1, ..., mn:Tn.` declarations of predicates, and SHALL record them in the program signature. In a program that declares kinds, types or predicates of its own, every global constant used in a clause or query SHALL be declared, either in the program, in an accumulated unit, in the standard library or by a registered builtin, and a use of an undeclared constant SHALL be reported as a load-time error naming the constant. In a program that declares none, an undeclared constant SHALL be treated as implicitly declared and reported as a warning, as the ELPI 1.18 oracle does; the command-line tool SHALL print the warning on standard error. Clause-local variables and `pi`-bound names SHALL NOT require declarations. Where ELPI 1.18 accepts or rejects a signature, the oracle's verdict is the reference.

#### Scenario: Undeclared constant is reported
- **WHEN** the program `pred p i:int.  p foo.` is loaded, where `foo` is declared nowhere
- **THEN** loading fails with an error that names the undeclared constant `foo`

#### Scenario: Undeclared constant in an untyped program is a warning
- **WHEN** the program `main :- X = (1 :: nil), print X.` is loaded, which declares nothing and uses `nil` as a list
- **THEN** loading succeeds and the load reports a warning that names `nil`
- **AND** the query `main` runs

#### Scenario: Kind and type declarations are accepted
- **WHEN** the program `kind nat type.  type z nat.  type s nat -> nat.  pred even i:nat.  even z.  even (s (s N)) :- even N.` is loaded
- **THEN** loading succeeds and the query `even (s (s z))` succeeds

### Requirement: Mode declarations
The loader SHALL accept the modes `i:` (input) and `o:` (output) on every argument of a `pred` declaration, defaulting to `o:` for arguments declared with `type`. When a clause is selected for a call, arguments in input position SHALL be matched, not unified: the clause head may instantiate its own variables but SHALL NOT assign any unification variable of the call's input argument, and a clause whose head would require such an assignment SHALL be treated as non-matching. Output arguments SHALL be unified as usual. The oracle's answers for mode-restricted calls are the reference.

#### Scenario: Input argument is matched not unified
- **WHEN** the program is `pred p i:int, o:int.  p 1 2.` and the query `p X Y` is solved with `X` unassigned
- **THEN** the query fails, because matching the input argument would require assigning `X := 1`
- **AND** the query `p 1 Y` succeeds with `Y = 2`

### Requirement: Prenex polymorphism
The typechecker SHALL support prenex (ML-style, rank-1) polymorphism: type variables written with an initial capital letter in `type` and `pred` declarations SHALL be implicitly universally quantified at the front of the declaration, and SHALL be instantiated independently at every use of the constant. Clauses SHALL be checked against the declared type with its type variables treated as rigid, and type variables SHALL be instantiated only with monomorphic or prenex-instantiated types, never with quantified types.

#### Scenario: Polymorphic predicate is used at two types
- **WHEN** the program declares `pred len i:list A, o:int.` with clauses `len [] 0.` and `len [_|T] N :- len T M, N is M + 1.`, and a clause body calls both `len [1, 2] N` and `len ["a"] M`
- **THEN** the program loads without type errors and the query yields `N = 2` and `M = 1`

### Requirement: Type abbreviations
The loader SHALL accept `typeabbrev name T.` and `typeabbrev (name A1 ... An) T.` declarations, and the typechecker SHALL expand abbreviations wherever they occur in declarations before comparing types, so that an abbreviation and its expansion are interchangeable. A cyclic abbreviation or a redefinition with a different body SHALL be reported as a load-time error.

#### Scenario: Abbreviation expands during checking
- **WHEN** the program declares `typeabbrev env (list (pair string int)).` and `pred lookup i:env, i:string, o:int.`, and a clause calls `lookup [pr "x" 1] "x" V`
- **THEN** the program typechecks, because the argument of type `list (pair string int)` matches the abbreviation `env`

### Requirement: Load-time type errors with positions
Typechecking SHALL run when a program is loaded or compiled, before any query is executed, and an ill-typed clause, query or declaration SHALL make loading fail. Every reported error SHALL carry the source position (file name, line and column) of the offending term and SHALL state the expected and the inferred type. No partially loaded program SHALL be returned when an error occurs.

#### Scenario: Ill-typed clause is rejected at load time
- **WHEN** the program `pred p i:int.  p "x".` is loaded
- **THEN** loading fails with a type error stating that `"x"` has type `string` where `int` is expected
- **AND** no program value is produced and no query is run

#### Scenario: Error reports the source position
- **WHEN** a file `bad.elpi` whose line 3 is `p "x".` is loaded after the declaration `pred p i:int.`
- **THEN** the error message contains `bad.elpi:3` followed by the column of the term `"x"`
