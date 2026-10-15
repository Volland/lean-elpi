---
title: What we took from ELPI's runtime to close the gap
date: 2026-10-15
author: Volodymyr Pavlyshyn
summary: A second round of profiling found the rest of LeanElpi's gap with ELPI in allocation, not in algorithms. Doing at load time what ELPI does at load time, and fusing two term traversals into one, took the geometric-mean slowdown from 2.4 to 1.9 times and the worst case from 10.5 to 4.6.
---
# What we took from ELPI's runtime to close the gap

[The previous article](/blog/why-leanelpi-was-slow/) took LeanElpi from 31 times slower than ELPI to about 3 times, by fixing three costs that had nothing to do with Lean. This one is about the rest. The profile had changed shape: no single function dominated any more, and the largest entry on every first-order program was memory management itself. That is a Lean question, and the answer came from reading ELPI's runtime.

## Result

Median wall time of three runs, in seconds, on the same Apple M2 Max, with the same harness and programs as before. "0.3.1" is the rerun after the previous article; "now" is this change. Teyjus was not installed for this run.

| Program | ELPI 1.18 | LeanElpi 0.3.1 | LeanElpi now | Now / ELPI | Speed-up |
|---|---|---|---|---|---|
| lambda3 | 0.28 | 2.84 | 1.29 | 4.6× | 2.2× |
| mu | 1.28 | 6.07 | 5.45 | 4.3× | 1.11× |
| crypt | 2.21 | 10.48 | 9.29 | 4.2× | 1.13× |
| fast_mu | 0.88 | 4.04 | 3.25 | 3.7× | 1.24× |
| cbn | 0.24 | 0.78 | 0.73 | 3.0× | 1.08× |
| queens | 0.90 | 3.26 | 2.63 | 2.9× | 1.24× |
| nrev 400 (ours) | 0.16 | 0.40 | 0.30 | 1.9× | 1.31× |
| fib 23 (ours) | 0.13 | 0.23 | 0.18 | 1.4× | 1.34× |
| cbv | 1.66 | 1.97 | 1.93 | 1.2× | 1.02× |
| church numerals (ours) | 0.08 | 0.11 | 0.09 | 1.1× | 1.20× |
| rev, rev14 | 0.17 | 0.21 | 0.18 | 1.1× | 1.18× |
| ackermann | 0.08 | 0.03 | 0.04 | 0.5× | – |

Over the thirteen programs both engines finish, the geometric-mean slowdown went from **2.4× to 1.9×**, and the worst case from 10.5× to 4.6×. On the stricter measure of the previous article (the eleven programs where ELPI needs more than 0.1 s) an independent rerun gave 3.0× before and 2.3× after, with the worst case at 4.6×. Peak memory did not change much (50 to 200 MB); the gains came from allocating less per step, not from holding less.

Seven of ELPI's performance programs still do not load: `index2`, `deep_index` and `dt` because the parser does not accept `:index(...)` before a `pred` declaration, `map_*` and `set` because of `macro`, `zebra` because of an undeclared `nil`. Those are front-end gaps, and the indexing ones hide exactly the programs where ELPI's deeper indexing would show.

## Where the time was

We sampled each slow program for two seconds at one millisecond (`sample` on macOS) and attributed each function's time to its caller. Four findings:

| Program | Hot spot | Share | Called from |
|---|---|---|---|
| queens, mu | freeing, allocating, reference counting | 40–45% | everywhere |
| lambda3 | `shiftUp`, relocating a term to a deeper scope | 38% | `deref` |
| lambda3 | comparing hypothesis keys | 9% | the call |
| crypt | the occurs check on a first-order binding | 14% | `solveFlex` |

The last one is not a gap. ELPI walks the term too (`hmove ~avoid`), so we left it alone.

The first one is the important one. OCaml allocates by bumping a pointer in a small young heap, and an object that dies young is never looked at again. Lean frees every object explicitly, when its reference count reaches zero, and freeing a term frees its children one by one. The same number of allocations costs Lean more than OCaml. Matching ELPI therefore means allocating *less* than ELPI does, and that is the rule this round followed ([the decision](https://github.com/volland/lean-elpi/blob/main/tg.md/decisions.md)).

## What ELPI does at load time

ELPI 1.18's runtime (`src/runtime.ml`) does three things once, when a clause is added, that LeanElpi did on every call.

**Clauses are compiled.** An ELPI clause is a record `{args; hyps; vars; mode}`: the head's arguments as a list and the body as a list of goals. LeanElpi kept the head and body as terms. Every call took the head apart again, and every instantiated body still contained its `,` spine, which the machine then took apart one step and two goal frames per conjunct. Clauses are now compiled when they enter the database: an array of head arguments and an array of body goals, with `true` dropped. Each goal gets the call's cut barrier, which is exactly what splitting `,` at run time did.

**Candidate lists are ready.** ELPI's `get_clauses` returns a list stored in its index: for each first-argument symbol, the clauses with that symbol *and* the clauses with a variable there, already merged in clause order. LeanElpi stored positions and merged the two lists on every call, then boxed each clause into a candidate record. Each key's array is now built once, and the choice point keeps a reference to it, not a copy.

**Hypotheses go into the index.** When ELPI runs `D => G` it compiles `D` and adds its clauses to the same per-predicate index. LeanElpi kept hypotheses in one list and checked every one of them on every call, for every predicate. In `lambda3` that is every typing hypothesis `of x A` checked against every typing goal, each with a different name. Hypotheses are now indexed by predicate and by first-argument key, with the variable-keyed ones kept apart and merged by insertion order, so a call sees only those that can apply.

## The traversal that ran twice

`lambda3` spent more than a third of its time in `shiftUp`, called from `deref`. LeanElpi names bound variables by de Bruijn *level*, so a term moved to a deeper scope keeps its free names but its own binders must move. Dereferencing a variable bound to `λx. b`, applied to arguments, therefore did two things: relocate the whole value to the current depth (`shiftUp`), then β-reduce it (`applyAt`). Each built a complete copy.

ELPI's answer to copying is sharing: its `move` returns the original node when nothing in it changed. We tried that first, on every traversal, and `lambda3` got **20% slower**. The reason is Lean's other trick. A term owned by nobody else is updated in place, so `applyAt` on the fresh result of `shiftUp` allocated almost nothing. Comparing the new node with the old one keeps the old one alive, and in-place update is no longer possible.

So the traversals split in two. Where the input is shared (a clause body stored in the database, a term being normalised), they keep sharing: instantiating a clause no longer copies its ground parts. Where the input is fresh, the fix is to stop building it twice: `applyAtFrom` substitutes the arguments and moves the remaining binders to their new depth in one pass. That alone took `lambda3` from 2.9 to 1.5 seconds, and from 40 to 23 billion instructions.

## Fewer boxes per step

The last two changes are small and very Lean-specific. Matching a clause head returned `Store × Array (Option Term) × Bool`. In Lean that is two pair objects per matched argument, plus a `some` box for every clause variable it bound, all freed a moment later. It now returns one record, and an unbound clause variable is marked by a placeholder term, not by `none`. That was 15% of `queens` and `mu`. The unifier's worklist had the same shape, `Term × Term × Nat`, and now holds one record per equation, skipping pairs that are the same object on both sides.

## What is left

The remaining factor of 3 to 4.6 on the slowest programs is no longer one thing. In `queens` and `mu` about 5% is the store checkpoint each clause attempt copies, where ELPI keeps a pointer into its trail and skips trailing altogether when no choice point is left (`last_call`). In `crypt` about 11% is the occurs check, which ELPI also does. The rest is the machine's own bookkeeping, spread across many small functions, and reference counting is still the largest single entry. The next steps are a lighter checkpoint, parsing `:index` so the indexing benchmarks run at all, and then multi-argument indexing.

None of these changes altered an answer. The oracle corpus (38 of 40, the same two registered divergences), the upstream suite (43 passed, no new failures) and the unit tests all pass unchanged. New tests check the parts that could have changed something: answer order with variable-headed clauses between keyed ones, cut in the middle of a compiled body, and that a goal is not slowed down by thousands of hypotheses about another predicate.

The requirements are in the OpenSpec change `optimize-clause-selection`, and the profile analysis and the comparison with ELPI's source are in its design document.
