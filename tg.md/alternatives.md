---
type: Decision
status: rejected
date: 2026-10-14
owner: Volodymyr Pavlyshyn
---
# Alternatives

Options considered and rejected during the design interview. Each one disagrees with an accepted decision, and that disagreement is recorded as a negative `-contradicts::` edge.

Keeping rejected options in the graph means a later proposal that revives one of them finds the reasoning here first, instead of repeating the debate.

## OCaml FFI engine

Link the upstream OCaml ELPI library into the Lean executable through C stubs, so ELPI semantics come for free.

Rejected because ELPI builtins could not call `MetaM`: it is a Lean monad stack, not a C function. It would also put two runtimes and two garbage collectors in one process, marshal every `Expr` across the boundary, need opam at build time, and fail inside the Lean server.

- status:: rejected
- -contradicts:: [[decisions#Native Lean engine]]
- motivated_by:: [[constraints#MetaM is not callable from C]]

## Out-of-process engine

Spawn the `elpi` binary and exchange serialized terms over pipes.

Rejected because ELPI could not query the Lean environment without a round-trip RPC for every builtin call, which is slow and is not embedding. It remains useful as the conformance harness, which runs the binary for comparison.

- status:: rejected
- -contradicts:: [[decisions#Native Lean engine]]

## Dependent types via CIC

Make Lean's own Calculus of Inductive Constructions the object theory of the dependent extension, so predicates range over arbitrary Lean types.

Rejected because unification modulo CIC conversion is undecidable and would rebuild Lean's elaborator inside the engine. It has no termination story and would duplicate `isDefEq` instead of reusing it.

- status:: rejected
- -contradicts:: [[decisions#LF as the dependent extension]]
- motivated_by:: [[constraints#CIC unification is undecidable]]

## Static Lean-typed signatures only

Declare predicates with Lean types, check clauses with Lean at load time, then erase types and run the plain engine.

Rejected as the dependent mechanism because it gives no proof terms and no certified search. LF checking subsumes it.

- status:: rejected
- -contradicts:: [[decisions#LF as the dependent extension]]

## Defeq suspension as the dependent mechanism

Suspend unification problems that need Lean's definitional equality as delayed constraints and discharge them with `isDefEq`.

Rejected as the main mechanism because it is incomplete and ties constraint scheduling to `MetaM` state. It survives only as the optional defeq bridge, a unification hook used from LF clauses.

- status:: rejected
- -contradicts:: [[decisions#LF as the dependent extension]]

## Mutable heap with trail

Bind uvars in mutable cells and undo bindings from a trail on backtracking, as WAM-style engines and upstream ELPI do.

Rejected for v1 because every Lean-side effect would need its own trail entry, and a forgotten entry is silent unsoundness. Adopted in the store after measurement, for unification bindings only: host effects still use the `Backtrackable` snapshot, so the objection no longer applies.

- status:: accepted
- motivated_by:: [[decisions#Persistent store]]

## Recursive CPS interpreter

Interpret goals with Lean recursion or success and failure continuations.

Rejected because deep searches overflow the native stack, cut needs ad-hoc escapes, and the search cannot be paused between solutions or stepped by a tracer.

- status:: rejected
- -contradicts:: [[decisions#Explicit abstract machine]]

## Porting upstream under LGPL

Translate the OCaml implementation and vendor the upstream `.elpi` standard library, accepting the LGPL-2.1.

Rejected because the whole project would become LGPL, unlike Lean and Mathlib, which are Apache-2.0.

- status:: rejected
- -contradicts:: [[decisions#Clean-room Apache license]]
- motivated_by:: [[constraints#Upstream ELPI is LGPL]]

## ELPI 2.x dialect

Target the current ELPI language with `func`, determinacy checking and the new type checker.

Rejected for now because the installed oracle is 1.18; a dialect without an oracle cannot be differentially tested. Revisit together with an oracle upgrade.

- status:: rejected
- -contradicts:: [[decisions#ELPI 1.18 dialect]]
- motivated_by:: [[constraints#Oracle is ELPI 1.18]]

## Everything as Expr

Cross the boundary only with reflected `term`s, so a user's `Shape` is `app (const "Shape.circle" []) [lit (nat 1)]` and no ELPI-side data types exist.

Rejected because the ELPI type checker then cannot tell a shape from a proof, every program pattern-matches on constant names, and results need a hand-written decoder. Plain derived types keep ELPI's checking and give a typed decoder for free.

- status:: rejected
- -contradicts:: [[decisions#Two-way type bridge]]
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
