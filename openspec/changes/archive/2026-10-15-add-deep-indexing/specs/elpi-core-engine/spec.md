## ADDED Requirements

### Requirement: Deep and multi-argument indexing
A `pred` declaration MAY be preceded by `:index (d1 … dn)`, where `di` is a number of levels or `_`. The engine SHALL then offer a call only the clauses, among the predicate's program clauses and its hypotheses, whose argument `i` is not rigidly incompatible with the call's argument `i` down to `di` levels, for every `i` with `di` positive, in clause order. Two terms SHALL be rigidly incompatible only when, within those levels, constants, literals or applications of constants differ; a clause variable, an unassigned variable, a λ-term or a bound name in either position SHALL stay compatible with anything. The specification SHALL NOT change which solutions a query has or their order, only how many clauses are tried.

#### Scenario: An index does not change the solutions
- **WHEN** the program `:index (3)  pred p o:list int.  p [1, 2, 3].  p [1, 2, 4].  p [_, 2, 5].  p [7, 8, 9].` is loaded and the query `p [1, 2, Z]` is solved for all solutions
- **THEN** the answers are `Z = 3`, `Z = 4` and `Z = 5`, in that order, as they are without the `:index` line

#### Scenario: Hypotheses are indexed like clauses
- **WHEN** the program `:index (2)  pred q o:list int.` is loaded and the query `[q [1, 2], q [1, 3], q [_, 4], q [9, 9]] => q [1, X]` is solved for all solutions
- **THEN** the answers are `X = 2`, `X = 3` and `X = 4`

#### Scenario: A later argument can be the only one indexed
- **WHEN** the program `:index (_ 1)  pred r i:int, i:int.  r A 1.  r A 2.  r A 3.` is loaded and `r 5 2` and `r 5 4` are solved
- **THEN** `r 5 2` succeeds and `r 5 4` fails
