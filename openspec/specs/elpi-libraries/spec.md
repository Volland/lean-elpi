# elpi-libraries Specification

## Purpose
The ELPI-side libraries shipped with LeanElpi and the way programs find them: a clean-room `std` library matching ELPI 1.18 behaviour, Lake-aware resolution of `accumulate` across packages, and libraries embedded in binaries.

## Requirements

### Requirement: Standard library
LeanElpi SHALL ship a clean-room standard library, written without copying upstream sources, that provides the `std` namespace of ELPI 1.18 under the same names and types, including at least the list predicates (`std.append`, `std.rev`, `std.length`, `std.mem`, `std.exists`, `std.forall`, `std.map`, `std.filter`, `std.fold`, `std.nth`, `std.split-at`, `std.zip`, `std.unzip`, `std.flatten`, `std.last`), control predicates (`std.do!`, `std.spy`, `std.assert!`, `std.findall`), and the `std.map` and `std.set` ordered-map and set structures. Like upstream, the standard library SHALL be available to every program without an explicit `accumulate`. Every standard predicate SHALL produce the same answers, in the same order and with the same determinism, as the ELPI 1.18 oracle, which is the reference.

#### Scenario: std list predicates behave like upstream
- **WHEN** the queries `std.append [1] [2] L`, `std.rev [1, 2, 3] R` and `std.appendR X Y [1, 2]` (all solutions) are solved
- **THEN** the answers are `L = [1, 2]`, `R = [3, 2, 1]`, and the three splits `X = [], Y = [1, 2]`, `X = [1], Y = [2]`, `X = [1, 2], Y = []` in that order, identical to the oracle
- **AND** `std.append X Y [1, 2]` has no solutions, as in the oracle, because the first two arguments of `std.append` are inputs

#### Scenario: std map operations
- **WHEN** the query `std.map.make cmp_term M0, std.map.add 1 "a" M0 M1, std.map.add 2 "b" M1 M2, std.map.find 1 M2 V` is solved
- **THEN** it succeeds with `V = "a"`, and the query `std.map.find 3 M2 W` against the same map fails
- **AND** the list combinator `std.map [1, 2] (x\ y\ y is x * 2) L` succeeds with `L = [2, 4]`

### Requirement: Lake-aware library resolution
`accumulate` targets SHALL be resolved by a library resolver that searches, in order: the directory of the accumulating file, the include paths given explicitly (for example with `-I`), the `lib/elpi/` directory of the current Lake package, the `lib/elpi/` directories of the Lake package's dependencies in manifest order, and finally the libraries embedded in the running binary. The first match SHALL win, and an unresolved accumulation SHALL be reported with the list of directories searched.

#### Scenario: Library from a dependency package is resolved
- **WHEN** a Lake package `app` depends on package `utils`, `utils` contains `lib/elpi/utils/lists.elpi` defining `pred twice i:list A, o:list A.`, and `app` loads a program containing `accumulate utils/lists.`
- **THEN** the accumulation resolves to the file in the `utils` package under `.lake/packages/utils/lib/elpi/`, and the query `twice [1] L` succeeds

### Requirement: Embedded libraries
The ELPI sources of the shipped libraries SHALL be embedded in the compiled Lean artefacts at build time, so that the CLI, compiled executables and runtime-library users resolve them without any library file present on disk. An on-disk file of the same name found earlier in the search order SHALL take precedence over the embedded copy.

#### Scenario: Binary resolves std without files on disk
- **WHEN** the installed `lean-elpi` binary is copied to an empty directory with no `lib/elpi/` folder and runs a program whose `main` calls `std.length [a, b] N, print N`
- **THEN** the program prints `2` and exits with status 0
