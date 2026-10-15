## ADDED Requirements

### Requirement: ELPI 1.18 surface syntax
The parser SHALL accept these forms of the ELPI 1.18 syntax. `macro @name X Y :- body.` defines a text macro, and every use `@name a b` SHALL stand for `body` with the arguments substituted, where an argument is one token or one balanced bracketed group. `pi x y z\ body` and `sigma x y\ body` SHALL stand for the nested single-name binders. A binder `x \ body` MAY have blanks before the backslash, except after the CHR keyword `rule`. A list MAY end with a comma before the closing bracket. An attribute such as `:index (1)` MAY precede a `pred` or `type` declaration.

#### Scenario: A macro with and without parameters
- **WHEN** the program `macro @n :- 3.  macro @twice X :- (X + X).  main :- Y is @twice @n, Y = 6.` is loaded and `main` is solved
- **THEN** it succeeds

#### Scenario: Several names in one binder
- **WHEN** the query `(pi x y\ x = x), (sigma A B\ A = 1, B = 2, A = 1)` is solved
- **THEN** it succeeds

#### Scenario: A binder with blanks and a list with a trailing comma
- **WHEN** the query `F = (x \ y \ x), [1, 2, ] = L, F 1 2 R` is solved
- **THEN** it succeeds with `R = 1` and `L = [1, 2]`

#### Scenario: An index attribute before a declaration
- **WHEN** the program `:index (1)  pred p i:int.  p 1.` is loaded and `p 1` is solved
- **THEN** it succeeds
