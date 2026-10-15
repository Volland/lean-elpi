---
title: Types across the boundary
date: 2026-10-15
author: Volodymyr Pavlyshyn
summary: LeanElpi can now share data types, functions and inductive declarations between Lean and λProlog in both directions.
---
# Types across the boundary

LeanElpi 0.1 let ELPI programs read and build Lean terms. This week it learned to share *data* in both directions.

## What is new

- `deriving Elpi` now works for parametric and recursive types. `Tree α` becomes `kind tree type -> type`, and `#elpi_signature Tree` shows the result. (It did not work for recursive types before. The documented example had a bug, now fixed and tested.)
- `elpi_data` defines Lean inductive types from ELPI `kind` and `type` declarations, so a type designed in the logic program needs no second definition.
- `elpi_extern` exposes an ordinary Lean function as an ELPI predicate, in three forms: total, `partial` (an `Option`) and `many` (a `List`).
- `lean.env.indt` and `lean.add_inductive` let ELPI read an inductive type completely and add a new one, with `casesOn`, `noConfusion` and friends, like Coq-Elpi's `coq.env.indt` and `coq.env.add-indt`.

The book has a new chapter, [Sharing types between Lean and λProlog](/book/interop/), with every example from the test suite.

## Why

Coq-Elpi works because declarations are data and host functions are typed predicates. We compared what it does with what LeanElpi did, and found three gaps: type parameters, a second copy of every type on the other side, and untyped glue code for host functions. All three are closed by one rule: **declare a type once, on either side, and generate the other.** The ELPI text of a type then has a single source, so round trips are tested properties.

Only plain data crosses. Indexed families, proofs and higher-order constructors are rejected with a message that points at `term` reflection or the LF layer. We prefer an error to a silent approximation.

## Next

Type classes. Lean instance resolution and ELPI clause resolution are both tabled proof search, and a bridge in either direction is the obvious next step.
