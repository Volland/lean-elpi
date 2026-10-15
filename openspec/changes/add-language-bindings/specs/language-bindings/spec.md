## ADDED Requirements

### Requirement: Handle-based C ABI
The library SHALL export `leanelpi_init`, `leanelpi_version`, `leanelpi_load`, `leanelpi_assert`, `leanelpi_free`, `leanelpi_solve` and `leanelpi_free_string`, declared in `leanelpi.h`. Programs SHALL be named by `uint64_t` handles. A failing call SHALL return `LEANELPI_INVALID` or `NULL` and store a message in its `err` out-parameter, which the caller releases with `leanelpi_free_string`. `leanelpi_solve` SHALL return JSON of the form `{"solutions":[{"bindings":{"X":"1"},"constraints":[]}],"exhausted":true}` with at most `limit` solutions (`0` meaning all) and `exhausted` false when the limit stopped the search. A fuel of `0` SHALL select the default budget.

#### Scenario: Load and query
- **WHEN** a program defining `n 1.` and `n 2.` is loaded and `n X` is solved with no limit
- **THEN** the answer lists two solutions binding `X` to `1` and `2`
- **AND** `exhausted` is true

#### Scenario: Limit stops the search
- **WHEN** `n X` is solved with limit 1
- **THEN** one solution is returned and `exhausted` is false

#### Scenario: Assertion is persistent
- **WHEN** `q 2.` is asserted into a program that defines `q 1.`
- **THEN** the new handle answers `q X` with `1` and `2`
- **AND** the original handle still answers with `1` only

#### Scenario: Errors are reported, not raised through C
- **WHEN** a program with a type error is loaded, or a query names an undeclared predicate, or a freed handle is used
- **THEN** the call fails and `err` holds the engine's message

#### Scenario: Handles are distinct under concurrency
- **WHEN** several threads load programs at the same time and each queries its own program
- **THEN** every thread gets the answers of its own program

### Requirement: Self-contained shared library
`scripts/build-ffi.sh` SHALL produce `dist/libleanelpi.dylib` or `dist/libleanelpi.so` and `dist/leanelpi.h`. The library SHALL contain the engine and SHALL depend only on the operating system's C and C++ runtime libraries and on the Lean runtime libraries that the build places in the same directory (none on macOS, where the runtime is linked in; `libleanshared` on Linux, whose toolchain archives cannot be linked into a shared object), so that it runs on a machine without a Lean toolchain.

#### Scenario: No Lean dependency at run time
- **WHEN** the dynamic dependencies of the built library are listed
- **THEN** none of them is a Lean, Lake or GMP library other than those shipped beside it

### Requirement: Python binding
The `leanelpi` Python package SHALL expose `Program`, `Solution`, `ElpiError` and `version`. `Program(source)` SHALL compile a program. `first`, `solve`, `solve_all` and `ask` SHALL query it, with `limit` and `fuel` options; a failed query SHALL be an empty result, not an exception. `assert_clause` SHALL return a new `Program`. Engine errors SHALL raise `ElpiError`. `close()` and the context manager SHALL free the handle, after which use SHALL raise `ValueError`. The package SHALL find the library in `$LEANELPI_LIB`, inside the package, or in `dist/` of a checkout.

#### Scenario: Query from Python
- **WHEN** `Program(APP).first("app [1,2] [3] R")` is called with the usual `app`
- **THEN** it returns `{"R": "[1, 2, 3]"}`

#### Scenario: Python failure and errors
- **WHEN** a query fails, and when a program with a type error is loaded
- **THEN** `first` returns `None` and loading raises `ElpiError`

#### Scenario: Closed program
- **WHEN** a program is closed and then queried
- **THEN** `ValueError` is raised

### Requirement: Node.js binding
The `@lean-elpi/leanelpi` npm package SHALL export `Program`, `ElpiError` and `version`, with TypeScript declarations. `new Program(source)` SHALL compile a program. `first`, `solve`, `solveAll` and `ask` SHALL query it with `limit` and `fuel` options; a failed query SHALL give `null` or an empty array. `assertClause` SHALL return a new `Program`. Engine errors SHALL throw `ElpiError`. `close()` SHALL free the handle. The package SHALL load the library from `LEANELPI_LIB`, from the matching `@lean-elpi/leanelpi-<os>-<cpu>` package, or from `dist/` of a checkout.

#### Scenario: Query from Node
- **WHEN** `new Program(APP).first("app [1,2] [3] R")` is called
- **THEN** it returns an object with `R` equal to `[1, 2, 3]`

#### Scenario: Node failure and errors
- **WHEN** a query fails, and when a program with a type error is loaded
- **THEN** `first` returns `null` and loading throws `ElpiError`

#### Scenario: Persistent assert from Node
- **WHEN** a clause is asserted
- **THEN** the new program sees it and the original does not

### Requirement: Rust binding
The `leanelpi` crate SHALL expose `Program`, `Solution`, `Error` and `version`, with `new`, `assert_clause`, `solve`, `solve_with`, `first` and `ask`. `Program` SHALL be `Send` and `Sync`. Dropping a `Program` SHALL free its handle. The build script SHALL link `libleanelpi` from `LEANELPI_DIST`, or from `dist/` of a checkout, and SHALL fail with instructions when it is not found.

#### Scenario: Query from Rust
- **WHEN** `Program::new(APP)?.first("app [1,2] [3] R")` is called
- **THEN** the solution binds `R` to `[1, 2, 3]`

#### Scenario: Shared across threads
- **WHEN** four threads query one `Arc<Program>`
- **THEN** each gets its own correct answer

### Requirement: Distribution
Releases SHALL publish a platform wheel to PyPI for each supported platform, one `@lean-elpi/leanelpi-<os>-<cpu>` npm package per platform together with the `leanelpi` loader package, and the `leanelpi` crate. The Python, npm and Cargo versions SHALL equal the version in `lakefile.lean`; `scripts/check-versions.sh` SHALL fail otherwise. A release workflow SHALL build, test and publish from a version tag, using trusted publishing for PyPI.

#### Scenario: Versions agree
- **WHEN** `scripts/check-versions.sh` runs on a consistent checkout
- **THEN** it exits 0
- **AND** after one binding's version is changed it exits non-zero

#### Scenario: Wheel carries the library
- **WHEN** the wheel is built on a platform
- **THEN** it is tagged `py3-none-<platform>` and contains `leanelpi/libleanelpi.*`

#### Scenario: Packages are publishable
- **WHEN** `twine check`, `npm pack` and `cargo package` run on the built artefacts
- **THEN** each succeeds
