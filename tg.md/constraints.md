---
type: Constraint
source: "per section: see each constraint's source:: line"
---
# Constraints

Rules nobody on this project chose: licenses, installed versions, platform limits and mathematical facts. Each one constrains decisions or components.

## Upstream ELPI is LGPL

The reference implementation of ELPI is distributed under LGPL-2.1, so porting or vendoring it makes the result a derivative work.

- source:: LICENSE file of the upstream ELPI repository (LPCIC/elpi)
- constrains:: [[decisions#Clean-room Apache license]]
- constrains:: [[decisions#Native Lean engine]]
- constrains:: [[components#Standard library]]

## Oracle is ELPI 1.18

The ELPI installed on the development machine through opam is version 1.18.2, which makes it the oracle that defines reference answers.

- source:: `elpi -version` in the opam default switch, 2026-10-14
- constrains:: [[decisions#ELPI 1.18 dialect]]
- constrains:: [[components#Conformance harness]]

## Lean toolchain 4.35

The project builds with Lean 4.35.0 (`leanprover/lean4:v4.35.0`); APIs such as `Meta.SavedState` and environment extensions follow that version.

- source:: `lean --version` via elan, 2026-10-14
- constrains:: [[decisions#Monad-generic core and packaging]]
- constrains:: [[components#Commands]]

## CIC unification is undecidable

Higher-order unification modulo the conversion of the Calculus of Inductive Constructions is undecidable in general; any unifier for it is a heuristic.

- source:: Huet 1973; Goldfarb 1981 (undecidability of second-order unification)
- constrains:: [[decisions#LF as the dependent extension]]
- constrains:: [[decisions#Plain types with reflected Lean terms]]

## Pattern unification is decidable

Higher-order unification restricted to Miller's pattern fragment is decidable and has most general unifiers, including in LF.

- source:: Miller 1991, "A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification"; Pfenning 1991 (LF)
- constrains:: [[decisions#LF as the dependent extension]]
- constrains:: [[components#Unifier]]

## MetaM is not callable from C

Lean's `MetaM` is a monad stack over Lean state, not a C function, so foreign code cannot call back into it during search.

- source:: Lean 4 FFI model (only `@[extern]`/`@[export]` functions cross the boundary)
- constrains:: [[decisions#Native Lean engine]]

## Kernel is the trust anchor

Only the Lean kernel decides whether a proof is valid; tactics, elaborators and the ELPI engine are untrusted producers of terms.

- source:: Lean 4 design (de Bruijn criterion)
- constrains:: [[decisions#Lossless reflection with opaque levels]]
- constrains:: [[decisions#LF as the dependent extension]]
- constrains:: [[components#LF export]]
- constrains:: [[components#Tactic bridge]]
