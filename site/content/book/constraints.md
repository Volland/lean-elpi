---
title: Constraints and CHR
order: 6
summary: Delayed goals, suspended unification, and constraint handling rules.
---
# Constraints and CHR

Some goals cannot run yet because they depend on a variable that is still unknown. LeanElpi can **delay** such goals and wake them when the variable is assigned.

## Delayed goals

```elpi
pred even i:int.
even N :- 0 is N mod 2, print "even" N.

main :-
  declare_constraint (even X) [X],
  print "after",
  X = 4.
```

`declare_constraint G [X]` suspends `G` on the variable `X`. The program prints `after` first. When `X = 4` assigns the variable, `even 4` runs at once, in order, and prints `even 4`. If a woken goal fails, the assignment fails and the engine backtracks, so suspended goals are real constraints, not comments.

The constraint store is part of the persistent state, so backtracking undoes suspensions as well.

## Constraint Handling Rules

A **CHR** program rewrites the store of constraints. Here is a solver for `≤` that collapses cycles:

```elpi
constraint leq {
  rule \ (leq X X).
  rule (leq X Y) \ (leq X Y).
  rule (leq X Y) \ (leq Y X) <=> (X = Y).
  rule (leq X Y) (leq Y Z) <=> (leq X Z).
}

pred leq o:int, o:int.
leq A B :- declare_constraint (leq A B) [A, B].

main :- leq A B, leq B C, leq C A, print A B C.
```

The rules mean, in order: reflexivity is dropped; duplicates are dropped; antisymmetry unifies; transitivity adds the composed constraint. Posting `leq A B`, `leq B C`, `leq C A` forms a cycle, so the solver unifies all three variables.

## Solver tiers

LeanElpi offers four ways to extend the engine with a solver. Pick the lowest tier that works.

| Tier | What | Use it for |
|---|---|---|
| T1 | CHR solvers written in ELPI | Declarative constraint solvers |
| T2 | Native builtins in Lean | Deterministic functions, such as `lean.infer` |
| T3 | Native constraint handlers | Solvers that need Lean data structures |
| T4 | Unification hooks | Teaching unification about an interpreted symbol |

T4 is how the LF layer evaluates `add 2 3` by Lean computation when unification gets stuck on it.
