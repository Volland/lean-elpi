# elpi-conformance Specification

## Purpose
Differential testing of LeanElpi against the upstream OCaml `elpi` 1.18 binary as an oracle: a shared corpus of ELPI programs, answer comparison, oracle version pinning and a register of known divergences.

## Requirements

### Requirement: Shared conformance corpus
The repository SHALL contain a corpus of ELPI programs under `tests/conformance/corpus/*.elpi`, each defining a predicate `main` that prints its answers to standard output. The corpus SHALL cover every ELPI 1.18 behaviour specified by the `elpi-core-engine`, `elpi-typechecker` and `elpi-libraries` capabilities. The harness `tests/conformance/run.sh` SHALL run every corpus program with both the oracle (`elpi -test FILE`) and LeanElpi (`lean-elpi -test FILE`), with a per-program timeout, and SHALL report a result for every program. (`-test` runs the nullary `main`; ELPI 1.18 `-exec main` passes an argument list and rejects a nullary `main` with a type error.)

#### Scenario: Every corpus program runs on both engines
- **WHEN** `tests/conformance/run.sh` is run with the corpus containing `append.elpi`, `cut.elpi` and `pattern.elpi`
- **THEN** each of the three programs is executed once by `elpi` and once by `lean-elpi`, and the summary lists one result per program

### Requirement: Differential answer comparison
For each corpus program the harness SHALL compare the standard output and the exit status of the two engines, after normalising only timing lines and the names the oracle chooses for printed eigenvariables and fresh variables. A program SHALL pass when both agree and fail otherwise; a failure SHALL print a unified diff of the two outputs and both exit statuses. The harness SHALL exit with status 0 only when no program fails.

#### Scenario: Matching answers pass
- **WHEN** both engines print `[1,2]` and exit with status 0 for `append.elpi`
- **THEN** the harness reports `append.elpi` as passed

#### Scenario: Divergent answers fail with a diff
- **WHEN** the oracle prints `1` then `2` and LeanElpi prints `2` then `1` for `order.elpi`
- **THEN** the harness reports `order.elpi` as failed, prints a unified diff showing the reordered lines, and exits with a non-zero status

### Requirement: Oracle version pinning
Before running any comparison, the harness SHALL query the oracle's version (`elpi -version`) and SHALL refuse to run unless it is an ELPI 1.18.x release, reporting the version found and the version expected. A missing oracle binary SHALL be reported the same way, and no program SHALL be reported as passed in either case.

#### Scenario: Unexpected oracle version is reported
- **WHEN** the `elpi` on the `PATH` reports version `2.0.0`
- **THEN** the harness exits with a non-zero status and the message states that ELPI 1.18.x is required and 2.0.0 was found, without running any corpus program

### Requirement: Known divergence register
The file `tests/conformance/divergences.md` SHALL list known, accepted divergences, each entry naming a corpus program, the observed difference and the reason (for example an upstream bug or deliberately unsupported deferred feature). A divergent program with a register entry SHALL be reported as a known divergence and SHALL NOT fail the suite; a register entry whose program now matches the oracle SHALL be reported as stale so that the entry can be removed.

#### Scenario: Registered divergence does not fail the suite
- **WHEN** `printing.elpi` diverges from the oracle and `divergences.md` contains an entry for `printing.elpi`, and every other program passes
- **THEN** the harness reports `printing.elpi` as a known divergence and exits with status 0
