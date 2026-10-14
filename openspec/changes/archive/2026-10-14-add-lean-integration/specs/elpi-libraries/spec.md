## ADDED Requirements

### Requirement: Lean API library
The library `lean`, loaded with `accumulate lean.` and shipped as `lib/elpi/lean.elpi`, SHALL declare the following, so that a program which accumulates it type checks against the Lean surface without declarations of its own:
- The reflection types: `term`, `name`, `binder`, `level` and `literal`, with all their constructors.
- The tactic types `goal` (`goal Ctx P Ty`), `decl` and `argument`.
- The signatures and modes of every `lean.*` builtin.
- Helpers written in ELPI: `copy` (structural term copy, which users can extend by adding clauses), `lean.mk_app` (application that keeps the spine flat) and `lean.subst` (instantiating a binder body).

Its declarations SHALL match exactly the encoding defined by the `lean-reflection` capability.

#### Scenario: lean library declares the term type
- **WHEN** a program accumulates `lean` and declares `pred head-const i:term, o:name.` with the clause `head-const (app (const N _) _) N.`
- **THEN** the program loads with no type errors
- **AND** the same program without `accumulate lean.` is rejected, because the type `term` and the constructor `app` are not declared

### Requirement: Tactic combinator library
The library `lean.ltac` (`lib/elpi/lean.ltac.elpi`) SHALL define `typeabbrev tactic (goal -> list goal -> prop)`, the basic tactics `lean.ltac.intro`, `lean.ltac.exact`, `lean.ltac.apply`, `lean.ltac.refine` and `lean.ltac.assumption`, and the combinators `lean.ltac.then`, `lean.ltac.thenl`, `lean.ltac.orelse`, `lean.ltac.try`, `lean.ltac.repeat` and `lean.ltac.focus`. The combinators SHALL behave like their Lean tactic counterparts:
- `then T1 T2` runs `T2` on every goal produced by `T1`.
- `thenl T Ts` runs the i-th tactic of `Ts` on the i-th goal and fails on a length mismatch.
- `orelse T1 T2` runs `T2` only if `T1` fails, and keeps no choice point into `T1`.
- `try T` never fails.
- `repeat T` applies `T` until it fails.
- `focus T` fails unless `T` closes its goal.

Proofs built through these tactics SHALL be checked by Lean as specified for ELPI tactics.

#### Scenario: then composes two tactics
- **WHEN** a tactic's `solve G _ Gs :- lean.ltac.then (lean.ltac.intro "h") lean.ltac.assumption G Gs.` is run with `by elpi intro_assume` on the goal `p → p`
- **THEN** the goal is closed with `Gs = []` and the proof term `fun h => h`

#### Scenario: orelse falls back on failure
- **WHEN** a tactic's `solve G _ Gs :- lean.ltac.orelse (lean.ltac.exact {{(0 : Nat)}}) lean.ltac.assumption G Gs.` is run on the goal `p` with `hp : p` in context
- **THEN** `exact` fails the type check, `assumption` closes the goal with `hp`, and no error is reported

### Requirement: Derive library
The library `lean.derive` (`lib/elpi/lean.derive.elpi`) SHALL provide ELPI derivers for `BEq`, `DecidableEq` and `Repr` on inductive types without indices. They generate the instance as a reflected term and add it with `lean.add_decl`. The package SHALL ship an exported command `elpi_derive <Class> <Type>` that runs these derivers. Every instance it generates SHALL be checked by the Lean kernel when it is added. Asking for a class or type shape that the derivers do not support SHALL report an error naming the unsupported case.

#### Scenario: Derived BEq instance is accepted by Lean
- **WHEN** `inductive Color | red | green` is followed by `elpi_derive BEq Color`
- **THEN** the kernel accepts an instance `BEq Color`, and `(Color.red == Color.red, Color.red == Color.green)` evaluates to `(true, false)`
