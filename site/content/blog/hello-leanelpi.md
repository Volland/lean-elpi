---
title: Announcing LeanElpi 0.1
date: 2026-10-14
author: Volodymyr Pavlyshyn
summary: The first release: an ELPI engine in Lean with constraints, Lean integration and kernel-checked LF proof search.
---
# Announcing LeanElpi 0.1

Today we publish the first release of LeanElpi, a clean-room implementation of the ELPI dialect of λProlog in Lean 4.

## What is in 0.1

- **The engine**: typed clauses, backtracking, `pi` and `=>` goals, higher-order pattern unification, modes, a standard library, a command-line tool and a lazy library API.
- **Constraints**: delayed goals, a backtrackable constraint store and CHR, with native handlers and unification hooks for extensions.
- **Lean integration**: expression reflection, quotations, tactics and commands written in λProlog, `deriving Elpi`, and a small DSL for rules.
- **The LF layer**: dependently typed signatures, proof terms for every answer, export to Lean inductives, kernel-checked certificates, search strategies, mode and totality checking, and a bridge to Lean computation.

## Try it

```lean
require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.1.0"
```

Then follow [Getting started](/book/getting-started/). New to λProlog? The [book](/book/) starts from scratch and explains why higher-order logic matters for [neuro-symbolic systems](/book/neuro-symbolic/).

## What to expect

This is a first release. The LF exporter has a deliberately small fragment, totality theorems cover one designated argument, and performance has not been tuned. The repository lists these limits, and the conformance suite documents where behaviour differs from upstream ELPI.

Issues and ideas are welcome on [GitHub](https://github.com/Volland/lean-elpi/issues).
