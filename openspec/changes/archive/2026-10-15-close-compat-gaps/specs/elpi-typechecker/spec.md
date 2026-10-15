## MODIFIED Requirements

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
