## Why

Eleven of the twenty-one ELPI performance programs, and 71 of the 114 upstream tests, were rejected by LeanElpi at load time (`tests/upstream/known-failures.md`). The benchmark could therefore only speak for the programs LeanElpi could read. The first errors were language and library gaps, not engine limits: `macro`, `pi x y\ …`, `:index(…)` on a declaration, a trailing comma in a list, a spaced binder `x \ body`, an undeclared constant (`nil`) that the oracle only warns about, and the `std.map`/`std.set` structures with ELPI's types, `std.int.map`/`std.int.set`, and `std.time`.

**Depends on:** `optimize-clause-selection` (archived).

## What Changes

- **`macro @name X Y :- body.`** defines a text macro, expanded on the token stream before parsing.
- **`pi x y z\ body` and `sigma x y\ body`** bind several names at once.
- **A binder may have blanks before the backslash** (`x \ body`), except after the CHR keyword `rule`.
- **A trailing comma in a list** (`[a, b, ]`) is accepted.
- **`:index(…)` before a declaration** is accepted and, as before a clause, only a hint.
- **An undeclared constant in an untyped program** (one that declares no kinds, types or predicates of its own) is a warning on standard error, as in the oracle, not an error. A program that declares types keeps the error.
- **Library:** `std.map` is a balanced (AVL) tree with the type `std.map K V` and `std.set` is built on it; `std.int.map` and `std.int.set` are the integer-keyed versions; `std.time G T` measures a goal with a new `gettimeofday` builtin.
- **Lake** now knows `lib/elpi/*.elpi` are inputs of the library; before, editing them left a stale library.
- **Bounded scope scan:** the first-order fast path of the unifier examines at most 4096 nodes of a term before it binds a variable to it, because an accumulator bound at every step would otherwise cost quadratic time; ELPI performs no occurs check at all.

## Capabilities

### Modified Capabilities
- `elpi-typechecker`: undeclared constants in untyped programs.
- `elpi-libraries`: the standard library's maps, sets and `std.time`.
- `elpi-core-engine`: a new requirement for the surface syntax above.

## Impact

**Motivating decisions:** [[decisions#Undeclared constants are an error only where the type is known]] is revised; [[decisions#ELPI 1.18 dialect]] is the reason for the syntax.

**Components changed:** [[components#Parser]], [[components#Type checker]], [[components#Standard library]], [[components#Unifier]].
