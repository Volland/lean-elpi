# Changelog

## Unreleased

### Added
- ELPI 1.18 syntax (OpenSpec change `close-compat-gaps`): `macro @name X :- body.`, `pi x y z\ body` and `sigma x y\ body`, blanks before a binder's backslash, a trailing comma in a list, `:index (...)` before a declaration.
- `:index (d1 … dn)` on a `pred` declaration is used (OpenSpec change `add-deep-indexing`): a call is offered only the clauses and hypotheses whose indexed arguments do not clash with its own to that depth. `dt` 18 s to 4 s, `index2` 47 s to 6 s.
- Library: `std.int.map`, `std.int.set`, `std.time` and the `gettimeofday` builtin; `std.map` is now a balanced tree with the type `std.map K V`.
- `tests/Core/Compat.lean`; the benchmark covers every ELPI performance program.

### Changed
- An undeclared constant in a program that declares no types is a warning (printed by the CLI), as in ELPI; programs that declare types keep the error.
- The unifier's fast path scans at most 4096 nodes of the term it binds a variable to (cyclic or out-of-scope bindings of larger terms are no longer caught; ELPI never checks).
- Lake rebuilds the library when `lib/elpi/*.elpi` changes.
- Upstream suite: 52 of 114 pass (was 43).

## 0.3.2 — 2026-10-15

### Changed
- Engine speed (OpenSpec change `optimize-clause-selection`): clauses are compiled at load time (head argument array, flat body goals); each first-argument key keeps a ready candidate array; hypotheses are indexed by predicate and key; dereferencing relocates and β-reduces a λ-term in one pass (`Term.applyAtFrom`); clause instantiation keeps ground subterms shared; head matching and the unifier allocate one record per step. On ELPI's performance programs the geometric-mean slowdown against ELPI went from 2.4 to 1.9 times and the worst case (`lambda3`) from 10.5 to 4.6. Conformance results are unchanged.

### Added
- `tests/Core/ClauseSelection.lean`; benchmark results `tests/bench/results/2026-10-15-clause-selection.json`; decision "Allocate less than OCaml"; blog post "What we took from ELPI's runtime to close the gap".

## 0.3.1 — 2026-10-15

### Added
- Benchmark harness `tests/bench/run.py` (LeanElpi, ELPI 1.18 and Teyjus on ELPI's performance programs), its results, and the blog posts "How compatible and how fast is LeanElpi?" and "Why LeanElpi was 30 times slower than ELPI, and what fixed it".
- `tests/Core/Scaling.lean`: guards against the engine copying its store or a term.
- Hypotheses added with `=>` are indexed by head and first argument (`Key.bound` for eigenvariables).

### Changed
- Engine speed and memory (OpenSpec change `optimize-engine-store`): head matching binds clause variables directly; the binding store is an array with an undo trail and choice points keep a checkpoint; a first-order fast path in the unifier; β-reduction substitutes all arguments in one pass. On ELPI's performance programs the geometric-mean slowdown against ELPI went from 31 times to 3 and peak memory from gigabytes to about 100 MB. Conformance results are unchanged.
- The requirement "Persistent store" states the behaviour (value semantics, restore on backtracking), not the representation; the design paper, the decision record and the performance section were updated.

## 0.3.0 — 2026-10-15

### Added
- Language bindings (`language-bindings` capability): Python (`ctypes`), Node.js (`koffi`, with TypeScript types) and Rust, over a handle-and-string C ABI (`Elpi/Ffi.lean`, `ffi/leanelpi.h`).
- `scripts/build-ffi.sh`: `libleanelpi` for macOS (runtime linked in, one file) and Linux (with `libleanshared` beside it).
- Packaging and release: platform wheels, per-platform npm packages under the `@lean-elpi` scope, the `leanelpi` crate, `scripts/package-*.sh`, `scripts/check-versions.sh`, `.github/workflows/release.yml` and `PUBLISHING.md`.
- Book chapter "From Python, Node.js and Rust".

## 0.2.0 — 2026-10-15

### Added
- Lean/ELPI type bridge (`lean-interop` capability): `elpi_data`, `elpi_extern` (total, `partial`, `many`), `#elpi_signature`.
- `lean.env.indt` and `lean.add_inductive` builtins (the Lean analogue of Coq-Elpi's `coq.env.indt` / `coq.env.add-indt`).
- Book chapter "Sharing types between Lean and λProlog", blog post, design paper `tg.md/papers/interop.md`.
- Package metadata (description, keywords, license, readme) for Lake and Reservoir.

### Changed
- `deriving Elpi` supports type parameters (ELPI type variables `A`, `B`, …) and nested occurrences.
- Derived declarations are loaded before registered builtin signatures, so builtins can mention derived types.

### Fixed
- `deriving Elpi` failed on every recursive type.

## 0.1.0 — 2026-10-14

First release: ELPI 1.18 engine, constraints and CHR, Lean integration, LF layer, upstream compatibility suite, documentation site.
