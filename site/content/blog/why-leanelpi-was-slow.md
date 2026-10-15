---
title: Why LeanElpi was 30 times slower than ELPI, and what fixed it
date: 2026-10-15
author: Volodymyr Pavlyshyn
summary: Profiling the LeanElpi engine found three specific costs, not a Lean limit. Fixing them took the geometric-mean slowdown against ELPI from 31 times to 3, and memory from gigabytes to about 100 MB.
---
# Why LeanElpi was 30 times slower than ELPI, and what fixed it

[The first benchmark](/blog/compatibility-and-performance/) put LeanElpi 0.3.0 at 4 to 142 times slower than ELPI, with memory use in gigabytes. We assumed that was the price of a persistent data structure in Lean, as the design paper had warned, and that the fix would be a large redesign. Profiling said otherwise. Three specific costs explained almost all of it, and each had a small fix. This article walks through them, because two are general lessons about unification and one is a general lesson about Lean.

The numbers below are for the development tree after the fixes, which is not yet a release. The conformance results did not change: 38 of 40 corpus programs and 43 of 114 upstream tests, the same programs as before.

## Result

Median wall time of three runs, in seconds, on the same Apple M2 Max, with the same harness and programs as the first article. "Before" is release 0.3.0.

| Program | ELPI 1.18 | LeanElpi before | LeanElpi now | Now / ELPI | Teyjus 2.1.1 |
|---|---|---|---|---|---|
| rev, rev14 | 0.18 | out of memory | 0.24 | 1.3× | 0.07 (rev14) |
| church numerals (ours) | 0.10 | 2.85 | 0.11 | 1.1× | – |
| cbv | 1.73 | 64.7 | 2.13 | 1.2× | – |
| fib 23 (ours) | 0.14 | 0.51 | 0.24 | 1.7× | – |
| nrev 400 (ours) | 0.17 | 7.53 | 0.39 | 2.3× | – |
| cbn | 0.26 | 33.7 | 0.84 | 3.2× | – |
| queens | 0.93 | 66.5 | 3.64 | 3.9× | 1.36 |
| fast_mu | 0.93 | 13.7 | 4.41 | 4.7× | 1.89 |
| crypt | 2.27 | 44.8 | 11.7 | 5.2× | 4.25 |
| mu | 1.27 | 35.9 | 6.65 | 5.2× | 3.40 |
| lambda3 | 0.30 | timeout (300 s) | 3.23 | 10.7× | – |

On the eight programs both versions could finish, the geometric-mean slowdown went from **31× to 3.1×**. Over all eleven programs where both engines finish now, it is 2.9×, and the worst case is 10.7×. Teyjus, the other λProlog system, is between 0.4 and 2.8 times ELPI's time on its six programs, so LeanElpi is now about 2 to 3.4 times Teyjus's time on the programs they share.

A second full run on the same build gave the same ratios to within 0.1 (geometric mean 3.0, worst case 10.5), with every engine about 10% faster in absolute time, so the ratios are the stable part. Both result files are in the repository.

Peak memory moved more:

| Program | ELPI | LeanElpi before | LeanElpi now |
|---|---|---|---|
| queens | 132 MB | 10.5 GB | 207 MB |
| cbv | 17 MB | 15.6 GB | 103 MB |
| mu | 17 MB | 6.8 GB | 119 MB |
| nrev 400 | 15 MB | 3.7 GB | 110 MB |
| rev | 44 MB | killed at 36 GB | 91 MB |

LeanElpi still uses several times ELPI's memory, partly the 50 MB baseline of the Lean runtime (a trivial program is 52 MB against ELPI's 15). It no longer uses memory in proportion to the work it has done.

## Cost 1: binding a variable rebuilt the whole term

The first article observed that memory grew with the work done. The sign of something worse was in a measurement we made on the way: appending two lists took time and memory that quadrupled when the lists doubled. A list append does a constant amount of work per element, so something walked the list at every step.

It was the unifier. Binding a unification variable `X := t` in higher-order pattern unification has to check that `t` only mentions names `X` may see, and to prune the variables in it that it may not. The implementation did this by *inverting* `t`: a function that returns a rewritten copy of the whole term. For `append (xcons X XS) L (xcons X L1)` the clause variable `L` is bound to the caller's entire remaining list on every step, so every step copied the list.

ELPI, like WAM-style engines, does not bind `L` through unification at all: the first occurrence of a variable in a clause head is simply recorded as "the goal's subterm at this position". There is no variable, no check, and no copy.

LeanElpi now does the same. Head matching (`hmatch`) walks the head against the goal. The first time it meets a clause variable it records the goal's subterm; only variables that are still unset after the head has matched become fresh unification variables, for the body. Any case it does not handle (a flexible goal argument, a head variable applied to arguments, hooks that may reinterpret a clash) falls back to the old path, so the semantics are unchanged.

One correctness detail: a variable bound directly to a λ and used under a binder must be relocated to the depth of its occurrence. An early version skipped that and printed a wrong answer for a higher-order test while passing every first-order one, which is why we compared printed answers with ELPI's on a small case before trusting any timing.

A smaller, related fast path: when the variable has no arguments and sits at the current depth, the unifier now scans the term read-only and assigns it as it is if nothing needs pruning, instead of rebuilding it.

Effect: `rev` went from out of memory to 1.3 times ELPI, and the quadratic growth disappeared.

## Cost 2: the persistent map copied a path of nodes on every binding

With cost 1 gone, a profile of `queens` was clear: 83% of the time was in two functions, one that copies an array and one that frees an object. Both were in the persistent hash map that held the bindings.

A persistent map shares structure between versions, so an update costs a path of node copies instead of a full copy. But each choice point kept the *previous* version, so the nodes along the path were shared with it and had to be copied, and then the old nodes freed when the choice point went away. Every binding paid for a path of four or five 32-wide nodes, on the order of a kilobyte. The design paper had expected a logarithmic factor; in practice the constant was the problem, and it was paid on every binding on programs that use choice points heavily.

The replacement is the structure WAM-style engines use. Bindings live in an array indexed by variable. Each binding that a choice point may have to undo is recorded on a *trail*. A choice point no longer keeps the store; it keeps a small *checkpoint*: the trail length, the variable count, and the persistent fields (the constraint store, the wake queue). Backtracking resets the trailed variables and truncates the arrays.

The original objection to a trail still stands for Lean-side effects: every effect a builtin has would need its own undo entry, and a forgotten entry is silent unsoundness. So the trail covers only unification bindings. The host monad's state (`MetaM` under Lean, a counter in a test) is restored exactly as before, from the snapshot each choice point already took.

The store still behaves as a value. If a caller keeps the store it passed in, the first write copies the arrays (Lean's copy on write), so `unify`, the builtin interface and the constraint handlers did not change.

## Cost 3: hypotheses were tried one by one

`lambda3` is a type-checking benchmark: a goal `of (lam F) (impl A B) :- pi x\ of x A => of (F x) B` adds a hypothesis `of x A` at every level, so a term with n nested lambdas runs with n hypotheses. Every goal was tried against every hypothesis, and each attempt dereferenced the goal's argument again, a variable applied to as many names as the depth. The cost grew about as the fourth power of the depth: a depth of 352 took 35 seconds for one type-check, where ELPI needs about 0.3 milliseconds (its whole thousand-fold run takes 0.3 seconds).

Two changes. First, hypotheses are indexed. ELPI's clause index covers hypotheses by their first argument too, so a goal about the name `x₇` never looks at a hypothesis about `x₃`. Each hypothesis now records its head predicate and first-argument key when `=>` adds it, and eigenvariables (the names `pi` introduces) are a key in their own right. A λ or a variable stays a wildcard, because η-expansion can make a λ equal to an applied name, and the index must never change which clauses *can* apply, only how many are tried. Second, β-reduction substituted arguments one at a time: applying a variable to *k* arguments cost O(k²), and `lambda3` applies variables to a growing number of them. It now substitutes all of them in a single traversal, and goal arguments are dereferenced once per call, not once for each clause tried.

The depth-352 type-check went from 35 seconds to 0.05; the full program, which does it a thousand times, from a timeout to 3.2 seconds. That is still 10 times ELPI, the largest gap left. A profile of it shows the time in dereferencing and substitution under a spine that grows with the depth, and in scanning the hypotheses, which we have not optimised further.

## The Lean lesson: who owns the array?

The trail only pays if an array update happens *in place*, and Lean updates an array in place only when nothing else holds a reference to it. Otherwise it silently copies the whole array first. The first version of the new store was correct and slower than the old one: every binding copied the arrays, so a doubling of the input quadrupled the time again, this time with memory flat.

We found two second references directly:

- **A `for` loop with an early `return`** keeps the loop's previous state in its result. The compiler's output for the head-matching loop showed the old store retained for the whole call, so every binding inside it copied.
- **A function that reports failure without returning the store** forces its caller to keep the old store alive, in case it is needed. `dbgTraceIfShared` showed the store shared on entry to the unifier's inversion step for exactly this reason. It now always returns the store, and undoes through a checkpoint when it has to delay.

We also removed two patterns we suspected, without being able to say how much each mattered, because the changes went in together: moving the store out of the machine record with a `let` (which did not help on its own), and running the attempt loop in monadic code, where continuations can capture the store. The store is now a separate parameter of the step functions, not a field of the machine; the loops that thread it are plain recursion in pure code; failed attempts hand the store back.

The tools were the compiler's intermediate representation (`set_option trace.compiler.ir.result true`, where an `inc` before a call is the second reference) and `dbgTraceIfShared`, which prints whenever an object is shared at that point. A regression test now appends two lists of about 80,000 elements (a 160,000-element result), runs a chain of 300 nested hypotheses and backtracks over 2,000 alternatives with 100,000 variables alive, each with a generous time bound. The first would have failed on 0.3.0 by running out of memory.

## What this does not change

Compatibility. The corpus and the upstream suite give the same results as before, because the engine accepts the same programs; eleven of the twenty-one performance programs are still rejected by the parser, the type checker or a missing builtin before they run, and the article on [compatibility](/blog/compatibility-and-performance/) lists the reasons.

And the numbers are still a single machine and three runs. The ratios are more stable than the seconds.

## What is left

Most of the remaining time is allocation: a clause body is rebuilt as a term on every call, and Lean's reference counting frees it again. The next steps, in the order we would take them, are compiling clause heads and bodies once instead of interpreting them, a "closed term" flag so substitution and the scope scan can skip ground subterms, compressing chains of pruned variables, and compacting the store in long deterministic runs, where the arrays still grow with every variable created. The design notes for the store were updated (`tg.md/decisions.md`, the engine paper), and the change is an OpenSpec change, `optimize-engine-store`, with the regression tests tied to its scenarios.

## Reproduce it

```bash
lake build
python3 tests/bench/run.py --runs 3 --json out.json    # add TEYJUS_BIN=... for Teyjus
tests/conformance/run.sh && tests/upstream/run.sh lean # compatibility is unchanged
lake test                                              # includes tests/Core/Scaling.lean
```

The raw results are in `tests/bench/results/`: `2026-10-15.json` for 0.3.0 and `2026-10-15-optimized.json` and `2026-10-15-rerun.json` for this tree. Issues and faster ideas are welcome on [GitHub](https://github.com/Volland/lean-elpi/issues).
