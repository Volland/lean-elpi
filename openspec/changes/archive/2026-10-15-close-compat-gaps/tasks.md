## 1. Syntax

- [x] 1.1 `macro` definitions and uses
- [x] 1.2 `pi x y\` and `sigma x y\`, spaced binders, trailing comma, `:index` before a declaration

## 2. Typing and library

- [x] 2.1 Undeclared constants in untyped programs are warnings; the CLI prints them
- [x] 2.2 Balanced `std.map`, `std.set`, `std.int.map`, `std.int.set`, `std.time`, `gettimeofday`
- [x] 2.3 Lake tracks `lib/elpi`
- [x] 2.4 Bounded scan in the unifier's fast path

## 3. Verification

- [x] 3.1 Upstream suite 43 to 52 of 114, no regressions; conformance and `lake test` unchanged
- [x] 3.2 `tests/Core/Compat.lean`
- [x] 3.3 Benchmark with all programs, results in `tests/bench/results`
