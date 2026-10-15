## MODIFIED Requirements

### Requirement: Standard library
LeanElpi SHALL ship a clean-room standard library, written without copying upstream sources, that provides the `std` namespace of ELPI 1.18 under the same names and types, including at least the list predicates (`std.append`, `std.rev`, `std.length`, `std.mem`, `std.exists`, `std.forall`, `std.map`, `std.filter`, `std.fold`, `std.nth`, `std.split-at`, `std.zip`, `std.unzip`, `std.flatten`, `std.last`), control predicates (`std.do!`, `std.spy`, `std.assert!`, `std.findall`), the timing predicate `std.time`, and the `std.map` and `std.set` ordered-map and set structures, with their integer-keyed forms `std.int.map` and `std.int.set`. The map and set structures SHALL be height-balanced, so that adding, finding and removing a key take a number of steps logarithmic in the size. Like upstream, the standard library SHALL be available to every program without an explicit `accumulate`. Every standard predicate SHALL produce the same answers, in the same order and with the same determinism, as the ELPI 1.18 oracle, which is the reference.

#### Scenario: std list predicates behave like upstream
- **WHEN** the queries `std.append [1] [2] L`, `std.rev [1, 2, 3] R` and `std.appendR X Y [1, 2]` (all solutions) are solved
- **THEN** the answers are `L = [1, 2]`, `R = [3, 2, 1]`, and the three splits `X = [], Y = [1, 2]`, `X = [1], Y = [2]`, `X = [1, 2], Y = []` in that order, identical to the oracle
- **AND** `std.append X Y [1, 2]` has no solutions, as in the oracle, because the first two arguments of `std.append` are inputs

#### Scenario: std map operations
- **WHEN** the query `std.map.make cmp_term M0, std.map.add 1 "a" M0 M1, std.map.add 2 "b" M1 M2, std.map.find 1 M2 V` is solved
- **THEN** it succeeds with `V = "a"`, and the query `std.map.find 3 M2 W` against the same map fails
- **AND** the list combinator `std.map [1, 2] (x\ y\ y is x * 2) L` succeeds with `L = [2, 4]`

#### Scenario: Maps and sets stay ordered through removal
- **WHEN** the integers 0 to 199 are added to a `std.int.set` in descending order and the multiples of 3 are removed
- **THEN** `std.int.set.elements` returns the remaining integers in increasing order and `std.int.set.cardinal` is 133

#### Scenario: A map of a thousand keys is searched in logarithmic steps
- **WHEN** the keys 0 to 999 are added to a `std.int.map` in increasing order
- **THEN** every key is found, and the height of the tree is at most 14, the bound of a balanced tree of that size

#### Scenario: std.time measures a goal
- **WHEN** `std.time (X = 1) T` is solved
- **THEN** it succeeds with `X = 1` and a non-negative float `T`
