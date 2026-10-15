# Changelog

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
