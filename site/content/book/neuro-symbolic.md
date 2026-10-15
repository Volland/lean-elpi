---
title: Higher-order logic and neuro-symbolic systems
order: 11
summary: Why binders, hypotheses and checkable derivations matter when learned and symbolic parts meet.
---
# Higher-order logic and neuro-symbolic systems

This last chapter steps back. Why would anyone building learning systems care about a logic programming language with λ-terms?

## What "higher-order" means here

**First-order logic** quantifies over individuals: "for every person x, …". **Higher-order logic** also lets variables stand for predicates and functions, and lets terms contain binders. In λProlog the useful core is *intuitionistic higher-order hereditary Harrop logic*: clauses and goals may contain `pi` (universal quantification) and `=>` (implication), and terms are simply typed λ-terms.

The practical effect is simple. Programs, proofs, specifications and formulas all have binders. In a higher-order setting the binder is a first-class thing that the engine understands, not an encoding that each program must reinvent.

## The neuro-symbolic setting

A neuro-symbolic system combines a neural component, which is flexible and statistical, with a symbolic one, which is exact and explainable. A typical loop looks like this:

1. A neural model **proposes**: a program, a proof step, a rewrite, a type annotation, a plan.
2. A symbolic component **checks, completes, or searches** around the proposal.
3. Only what passes the check is trusted.

The weak point is step 2. The check has to be *sound* (never accepts nonsense) and *expressive* (can talk about the structured things the model produces: programs with variables, formulas with quantifiers, proofs with hypotheses).

## Why higher-order logic fits

**Structured outputs have binders.** Code, formulas and proofs contain scoping. First-order encodings force every tool to implement substitution and renaming correctly, and bugs there are subtle and silent. With HOAS, `lam (x\ …)` carries scope in the representation, and pattern unification handles it.

**Hypothetical reasoning is built in.** "Assume this lemma, then show that" is the goal `A => G`. "For an arbitrary x, show P(x)" is `pi x\ P x`. These are exactly the moves that a proof-producing model makes, and the engine executes them directly.

**Search with constraints.** A model rarely proposes a complete object. It proposes a sketch with holes. Holes are unification variables, and the engine fills them by search. Constraints (the previous chapters) let the search wait when a hole is not determined yet instead of guessing.

**Declarative rules are inspectable.** A rule such as `of_lam` is a readable statement of a typing rule. Domain experts can audit and extend rules without touching the engine, and a model can learn to propose *applications* of rules rather than raw strings.

**Derivations are objects.** This is the key point for trust. If the symbolic search records a derivation, the derivation is a term that an independent checker can verify. That is what the LF layer does.

## Where trust should live

The de Bruijn criterion says: let the search be as clever and unverified as you like, as long as what it outputs is checked by a small trusted kernel. In LeanElpi:

- the neural model may be wrong, and the search engine may be wrong;
- the proof term the engine records is translated to a Lean term;
- **the Lean kernel decides.** A wrong certificate is rejected, and a correct one becomes a theorem with no extra axioms.

So a neuro-symbolic pipeline can use a model to *guide* the choice of rules or strategies, and use LeanElpi to *carry out and certify* the search. The model never has to be trusted, and the symbolic part never has to be reimplemented in a verifier.

## A concrete picture

Imagine a model that suggests a typing derivation for a program in a small language. You encode the language as an LF signature, as in the previous chapter. The model's suggestion becomes a query or a strategy hint. The engine searches within it, and `lf_certify` produces a theorem. If the model hallucinated a step, the search fails or the kernel rejects; if it was right, you get a machine-checked proof for free.

## What this release does not claim

LeanElpi does not contain a neural model, and it does not train anything. It provides the symbolic half: a higher-order logic engine with binders, constraints, and kernel-checked certificates. How you connect a learned component to it is up to your application; the natural seams are the query interface, strategies, and Lean tactics written in λProlog.

## Further reading

- Dale Miller and Gopalan Nadathur, *Programming with Higher-Order Logic* (2012).
- Dale Miller, *A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification* (1991).
- Frank Pfenning, *Logical Frameworks*, in the Handbook of Automated Reasoning.
- The ELPI project: github.com/LPCIC/elpi.
