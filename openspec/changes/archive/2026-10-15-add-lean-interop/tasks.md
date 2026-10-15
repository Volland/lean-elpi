## 1. Deriving

- [x] 1.1 Type parameters and ELPI type variables in `deriving Elpi`
- [x] 1.2 Recursive and nested occurrences through a local instance
- [x] 1.3 Indexed families rejected with a pointer to LF
- [x] 1.4 `#elpi_signature`

## 2. ELPI to Lean

- [x] 2.1 `elpi_data`: kinds and constructors to inductives and structures
- [x] 2.2 Errors for higher-order arguments, unknown types and missing constructors

## 3. Lean to ELPI

- [x] 3.1 `ElpiFn` and the `Extern` helpers
- [x] 3.2 `elpi_extern` in total, `partial` and `many` forms
- [x] 3.3 Builtin signatures that mention derived types (registry and assembly order)

## 4. Inductive types from ELPI

- [x] 4.1 `lean.env.indt` and the `lean.indt`/`lean.ctor` terms
- [x] 4.2 `lean.add_inductive` with the auxiliary constructions, command phase only

## 5. Documentation and tests

- [x] 5.1 Tests under `tests/Interop/`
- [x] 5.2 tg.md paper, component and decision
- [x] 5.3 Site article
