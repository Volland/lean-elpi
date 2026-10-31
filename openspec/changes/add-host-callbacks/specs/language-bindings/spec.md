## ADDED Requirements

### Requirement: Host callback predicates
The library SHALL export `leanelpi_declare`, which declares a host predicate from signature source on a new handle (leaving the old one valid), and `leanelpi_solve_host`, which runs a query like `leanelpi_solve` but answers every call to a declared host predicate by calling the given `leanelpi_host_fn` synchronously on the calling thread. The callback SHALL receive the predicate name and a JSON array with one term per argument, and SHALL return a `malloc`-allocated JSON string that the library frees: `{"rows":[[term,...],...]}` with one term per output-mode argument, or `{"error":"message"}`; `NULL` SHALL mean no rows. Row terms SHALL be constants known to the program, applications of them and literals; anything else SHALL be a runtime error. A host predicate called through `leanelpi_solve` SHALL fail with an error. Running out of fuel SHALL fail with an error message that starts with `out of fuel`.

#### Scenario: Host predicate answers a recursive query
- **WHEN** a program defines `path` recursively over a declared host predicate `edge`, and the host answers each call with the edges leaving its bound first argument
- **THEN** `path a X` returns every node reachable from `a`, in depth-first order, and the run is exhausted

#### Scenario: Host errors are reported
- **WHEN** the host answers with an error, with a constant the program does not know, or with a row of the wrong length
- **THEN** the run fails with a message naming the predicate and the problem

#### Scenario: Panics do not cross the boundary
- **WHEN** the Rust closure answering a host predicate panics
- **THEN** the run fails with an error that carries the panic message, and the library stays usable

#### Scenario: Host predicate without a host
- **WHEN** a query that reaches a declared host predicate runs through `leanelpi_solve`
- **THEN** the call fails with an error instead of crashing

#### Scenario: Out of fuel is distinguishable
- **WHEN** a run with or without a host exceeds its fuel budget
- **THEN** the error message starts with `out of fuel` and the Rust `Error::is_out_of_fuel` holds
- **AND** a run that finishes reports the fuel it used

### Requirement: Structured answers
Every solution in the JSON of `leanelpi_solve` and `leanelpi_solve_host` SHALL carry `"terms"`, the fully dereferenced binding of each query variable as a JSON tree: `{"c":name}` a constant, `{"c":name,"a":[...]}` a constant applied, `{"i":n}`, `{"f":x}`, `{"s":text}` literals, `{"v":name}` an unassigned variable and `{"o":printed}` anything else. Both answers SHALL report `"fuelUsed"`.

#### Scenario: Terms decode by kind
- **WHEN** a solution binds an integer, a string, an application, a list, a float, a λ-term and an unassigned variable
- **THEN** the Rust binding decodes them as `Int`, `Str`, `App`, a `::` / `[]` list, `Float`, `Other` and `Var`
- **AND** terms the host returns reach the solution unchanged
