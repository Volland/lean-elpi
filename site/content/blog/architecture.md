---
title: How LeanElpi is built: architecture of a λProlog engine in Lean
date: 2026-10-14
author: Volodymyr Pavlyshyn
summary: The layers of LeanElpi, from the term store and the abstract machine to solver tiers, the Lean bridge and the LF certificate pipeline.
---
# How LeanElpi is built

LeanElpi is a λProlog engine written in Lean 4. It has to do four jobs at once: be a faithful ELPI 1.18, be usable as a plain library, embed in Lean's metaprogramming, and certify proof search with the kernel. This article walks through the design and the reasons behind it.

## The layers

```text
 Lean files            ELPI / #lf source           CLI
      │                      │                      │
 Lean integration ── Front end (parser, type checker) ──┐
 (reflection, tactics,       │                          │
  commands, builtins)   Abstract machine ── Solver tiers T1–T4
      │                      │
      └──── Term store, persistent substitution, constraint store
                             │
                    LF layer: checker, proof terms, export, certificates ──► Lean kernel
```

Each layer only depends on the ones below. The engine core does not mention `MetaM`: it is generic over a `Backtrackable` monad, so the same code runs as a pure function, in `IO`, or inside Lean's metaprogramming monads.

## Terms and the persistent store

Terms are first-order trees extended with λ and with unification variables. Bound variables use **de Bruijn levels** (counted from the outside), and every unification variable records the level at which it was created. Levels make the scope rule cheap to enforce: a variable may only be assigned a term whose names are all older than the variable.

The substitution lives in a **persistent store**. Assigning a variable produces a new store and leaves the old one intact. Backtracking, which is the hot operation in logic programming, is then "go back to the store you saved", with no trail to unwind and no undo bugs. The same store holds the constraint store, so suspended goals backtrack with everything else.

## Unification

The unifier implements Miller's **pattern fragment**. When a variable is applied to distinct bound variables, the equation has a most general solution, and the unifier computes it, pruning variables from the other side when necessary so that scope is respected. When an equation falls outside the fragment, the unifier does not guess: it **delays** the problem on its flexible variables and resumes it when one of them is assigned. This keeps unification complete where it is decidable and honest where it is not.

## The abstract machine

Solving a goal is done by an **explicit abstract machine**: a record of the current goal list, choice points, program, and a fuel counter, advanced by a small `step` function. There is no host recursion in the search, which gives three properties we wanted:

- **Fuel.** Every step costs one unit, so runaway programs stop with a resource error rather than hanging.
- **Lazy answers.** The machine can be suspended after an answer and resumed for the next. Queries return lazy streams.
- **Auditable order.** Clauses are tried top to bottom, depth-first. Clause lookup uses a first-argument index respecting modes, and the order of answers matches ELPI.

Cut, `pi`, `=>`, and the logical connectives are goal forms handled directly by the machine. `pi x\ G` allocates a fresh level; `A => G` pushes a clause that is removed when `G` finishes.

## Front end

The parser and type checker implement the ELPI 1.18 dialect, including overloading and modes. The type checker runs before execution, so mistakes surface with a position. A clause is compiled to an indexed form, and a program is a persistent database that new units can extend, which is how accumulation and Lean's incremental file elaboration work.

## Solver tiers

Not every problem fits resolution. The engine exposes four tiers of extension:

1. **T1: CHR solvers in ELPI.** Constraint Handling Rules rewrite the constraint store.
2. **T2: native builtins.** Deterministic predicates implemented in Lean.
3. **T3: native constraint handlers.** A Lean function receives constraints and the store and decides what to keep, wake, or propagate.
4. **T4: unification hooks.** When unification gets stuck on an *interpreted* symbol, a hook may solve, suspend, or reject it.

The tiers are ordered by how much power, and how much responsibility, they give. A rule of thumb in the project: use the lowest tier that works.

## Talking to Lean

Lean expressions are **reflected** into ELPI terms: constants, applications, sorts, literals, and λ/∀/let as HOAS binders. Universe levels are opaque handles. The reflection is round-trippable, so a program can take a goal apart, build new terms, and hand them back.

On top of that sit the conveniences: `{{ … }}` quotations elaborated by Lean and spliced with antiquotations, the `lean.*` builtins that run in `MetaM`, tactics defined by a `solve` predicate, commands, and `deriving Elpi` for moving your data types across. Programs are compiled when declared and stored in an environment extension, so imports replay them.

## The LF layer and certificates

LF is where the project goes beyond ELPI. It is opt-in per file (`#lf`) and adds four things.

**Checking.** A bidirectional checker for the dependently typed λ-calculus λΠ: it reconstructs implicit arguments, reports expected and found types with positions, and infers whether each family is *syntax* or a *judgment*.

**Proof terms by elaboration.** The key design choice: instead of adding a trace log to the machine, each LF predicate `of M A` is elaborated at load time into `lf.of D M A`, where `D` is a **proof hole** bound by resolution. `pi` and hypotheses add λs over the hole. The machine itself does not change. Partial proof terms live in the persistent store, so backtracking discards them automatically.

**Export.** Lean forbids the direct HOAS encoding `lam : (Tm → Tm) → Tm` (a negative occurrence). We export syntax with binders as **scope-indexed** families, `Tm : Nat → Type`, with a generated `Var`, and hypothetical judgments take an explicit context, `Of : Ctx n → Tm n → Tp → Prop`, looked up through an inductive relation. Only fresh inductives and `Nat.succ` appear, so the kernel checks everything by structural conversion.

**Certificates.** A proof term is translated to a fully explicit constructor application and submitted with `addDecl`. If the kernel rejects it, the environment is left unchanged. This is the **trust boundary**: the parser, checker, machine and exporter may all have bugs, but none of them can cause a false theorem.

Around this core are search strategies (bounded and iterative deepening, with a derivation depth per LF goal in the machine), mode checking, totality checking whose theorems are only emitted with kernel-checked proofs, and the defeq bridge, which uses a T4 hook to let Lean evaluate bridged functions.

## How we test it

- **Spec-driven.** Every requirement and scenario of the OpenSpec specification is traced to code (`implements`) and to a test (`verifies`), and a gap report must be empty.
- **Oracle conformance.** A corpus of ELPI programs is run on the real ELPI 1.18 and on LeanElpi, and the outputs are compared. Known differences are registered in a divergence file.
- **Kernel as test oracle.** For the LF layer, the strongest test is that the kernel accepts the certificates, and rejects deliberately corrupted ones.

## Why Lean, and what it costs

Writing the engine in Lean gives portability and, above all, direct access to the kernel for certification. The cost is that Lean is a total language: the machine's loop is `partial` and bounded by fuel, and some performance tricks of the OCaml original (mutable arrays on the hot path) are replaced by persistent structures. We took that trade deliberately for correct backtracking and simple certification, and measure before optimising.

The source, specs and design notes are on [GitHub](https://github.com/Volland/lean-elpi).
