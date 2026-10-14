---
title: Terms, clauses and search
order: 3
summary: Facts, rules, unification, backtracking, cut and arithmetic.
---
# Terms, clauses and search

If you know Prolog, this chapter is a quick refresher with ELPI's syntax. If you do not, it is all you need to read programs in the rest of the book.

## Facts and rules

A program is a list of **clauses**. A clause `head :- body.` says: to prove `head`, prove `body`. A clause with no body is a **fact**.

```elpi
kind person type.
type ann, bob, carl person.

pred parent o:person, o:person.
parent ann bob.
parent bob carl.

pred ancestor o:person, o:person.
ancestor X Y :- parent X Y.
ancestor X Z :- parent X Y, ancestor Y Z.
```

Names starting with an uppercase letter (`X`, `Y`) are **unification variables**. Lowercase names (`ann`, `parent`) are constants. A comma means "and", a semicolon means "or".

## Queries and backtracking

A query is a goal. The engine tries the clauses of a predicate in order, top to bottom. If a clause leads to failure, it **backtracks** to the most recent choice and tries the next clause. Asking `ancestor ann X` yields `X = bob`; asking for more yields `X = carl`.

LeanElpi explores in this fixed depth-first order. The answers come back as a lazy stream, so you pay only for the answers you look at.

## Unification

Unification makes two terms equal by assigning variables. `parent ann X` matches the fact `parent ann bob` by assigning `X := bob`. Terms are built from constants, applications such as `app M N`, lists `[1, 2, 3]` (with `[H|T]` for head and tail), numbers, strings, and λ-abstractions, which the next chapter explains.

## Lists and recursion

```elpi
pred append i:list A, i:list A, o:list A.
append [] L L.
append [X|Xs] L [X|R] :- append Xs L R.

main :- append [1,2] [3] L, print L.
```

Running this prints `[1, 2, 3]`. The `A` in `list A` is a type variable, so `append` works on lists of anything.

## Arithmetic and comparison

`is` evaluates an arithmetic expression:

```elpi
pred len i:list A, o:int.
len [] 0.
len [_|T] N :- len T M, N is M + 1.
```

Comparisons such as `X >= Y` and `X < Y` are goals that succeed or fail.

## Cut

The cut `!` commits to the current clause: it discards the remaining clauses of the predicate and the choice points created so far in the body.

```elpi
pred max i:int, i:int, o:int.
max X Y X :- X >= Y, !.
max _ Y Y.
```

`max 3 7 M` gives `M = 7`: the first clause fails at `3 >= 7`, so the second applies. Use cut sparingly; modes (chapter on types) often express the same intent more clearly.

## Printing and `main`

`print` writes its arguments to the output. The predicate `main` is the conventional entry point when you run a file with `-test`:

```elpi
main :- ancestor ann carl, print "ann is an ancestor of carl".
```
