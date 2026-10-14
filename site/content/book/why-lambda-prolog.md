---
title: Why λProlog
summary: What λProlog adds to Prolog, and where ELPI and LeanElpi fit.
order: 1
---
# Why λProlog

Prolog is good at search over first-order data. It is awkward as soon as the data has binders, such as the λ in a λ-term, the ∀ in a formula, or the `fun` in a Lean expression. λProlog fixes this by making binders part of the language.

## Prolog plus λ-terms plus two new goals

λProlog extends Prolog in three ways:

1. **Terms are typed λ-terms.** `lam (x\ app x x)` is data, and `x\ …` is a binder the language understands.
2. **Unification is higher-order.** It can solve `F x = app x x` for `F`, which is how a program pulls a term apart under a binder.
3. **Goals can introduce names and assumptions.** `pi x\ G` runs `G` with a fresh name `x`, and `A => G` runs `G` with the extra clause `A`.

With these, a program about a language with binders can borrow the binders of the host language. No de Bruijn indices, no capture-avoiding substitution, no freshness side conditions: the logic does it.

## ELPI

ELPI is an extended, fast implementation of λProlog by the Inria and Coq-Elpi community. It adds modes (`i:` and `o:` annotations), constraint handling rules, and a rich standard library. Coq-Elpi uses it to write Coq plugins and tactics.

## LeanElpi

LeanElpi is a **clean-room** Lean 4 implementation of the ELPI 1.18 dialect: no upstream code is ported. It exists for three reasons.

- **Embedding.** Lean's own metaprogramming is powerful but low-level. A declarative language with binders is a better fit for many tactics and program transformations.
- **Trust.** A search engine can be wrong. In Lean, the kernel can check what the engine finds.
- **Portability.** The engine is plain Lean, with no foreign code, so it runs wherever Lean does.

The engine is generic over a backtracking monad. It works as a pure library, from a command-line binary, and inside `MetaM`.

## What this book covers

- the language: [terms and clauses](/book/first-programs/), [higher-order programming](/book/higher-order/), [types and modes](/book/types-and-modes/), [constraints](/book/constraints/);
- the tool: [standalone use](/book/standalone/) and [use inside Lean](/book/inside-lean/);
- the LF layer: [certified proof search](/book/lf/);
- the bigger picture: [higher-order logic and neuro-symbolic systems](/book/neuro-symbolic/).
