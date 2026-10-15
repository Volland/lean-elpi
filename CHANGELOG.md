# Changelog

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
