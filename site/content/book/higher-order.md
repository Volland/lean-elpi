---
title: Higher-order programming
order: 4
summary: Binders as data, pi and implication goals, and pattern unification.
---
# Higher-order programming

This chapter is the heart of λProlog. Everything here is impossible or painful in plain Prolog.

## Terms with binders

Suppose we want to represent the λ-calculus. We declare a type of terms and give `lam` a **function** as its argument:

```elpi
kind tm type.
type app tm -> tm -> tm.
type lam (tm -> tm) -> tm.
type c tm.
```

The term `lam (x\ app x x)` is a λ-term whose body mentions the bound variable `x` twice. The notation `x\ body` is ELPI's own λ-abstraction. The argument of `lam` has type `tm -> tm`, so the language, not our program, tracks scope. This style is called **higher-order abstract syntax** (HOAS).

## Beta reduction for free

Applying a bound function substitutes its argument:

```elpi
pred beta i:tm, o:tm.
beta (app (lam F) A) (F A).
```

`beta (app (lam x\ app x x) c) R` gives `R = app c c`. We wrote no substitution function: `F A` is an application in the metalanguage, and the engine reduces it.

## Going under binders: `pi`

How do we write a predicate that walks inside a λ? We need a name for the bound variable. The goal `pi x\ G` runs `G` with a **fresh constant** `x` that exists only inside `G`:

```elpi
pred id i:tm, o:tm.
id c c.
id (app A B) (app A' B') :- id A A', id B B'.
id (lam F) (lam G) :- pi x\ id x x => id (F x) (G x).
```

Read the last clause: to copy `lam F`, pick a fresh `x`, **assume** `id x x`, and copy the body `F x` into `G x`. The assumption `id x x` is a temporary clause that exists only while the goal runs. This is the second new goal form: `A => G` adds clause `A` for the duration of `G`.

Running `id (lam x\ app x c) S` prints `S = lam c0 \ app c0 c`. Fresh variables are printed as `c0`, `c1` and so on.

## Type checking a λ-calculus

The same two goals give the classic type checker:

```elpi
kind ty type.
type arr ty -> ty -> ty.
type nat ty.

pred of i:tm, o:ty.
of (app M N) B :- of M (arr A B), of N A.
of (lam F) (arr A B) :- pi x\ of x A => of (F x) B.
```

For `lam F`, we assume that a fresh `x` has type `A`, then check the body. The typing context is the set of assumptions, managed by the engine. There is no explicit environment and no variable-capture bug to write.

## Pattern unification

Higher-order unification is undecidable in general. λProlog programs stay in a decidable fragment called **patterns** (Miller 1991): a variable applied to *distinct bound variables*, such as `F x` where `x` is a fresh `pi` name. Within it, unification has a most general solution.

For example, with `x` fresh, unifying `F x = app x x` assigns `F := y\ app y y`. That is how a program decomposes `lam F` into pieces without ever writing a traversal.

Outside the fragment (for instance `F (app c c) = c`, which has several solutions) LeanElpi does not guess. It **suspends** the problem as a delayed goal and keeps going. The [constraints chapter](/book/constraints/) explains what happens then.

## Scope: why names cannot escape

A variable created outside a `pi` cannot capture a name created inside it. If you try to bind `Y` to a fresh `x` from outside the `pi`, unification fails, because `x` is not in the scope of `Y`. The engine enforces this with de Bruijn *levels* attached to every unification variable. It is what makes HOAS programs correct by construction.
