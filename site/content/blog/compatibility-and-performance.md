---
title: How compatible and how fast is LeanElpi? Test results against ELPI and Teyjus
date: 2026-10-15
author: Volodymyr Pavlyshyn
summary: LeanElpi 0.3.0 against ELPI 1.18 and Teyjus: what ELPI's own test suite says about compatibility, and a benchmark that shows LeanElpi is about 30 times slower and hungry for memory.
---
# How compatible and how fast is LeanElpi?

> **Update, the same day.** These are the numbers for release 0.3.0. We then profiled the engine and found that the slowdown came from three specific costs, not from Lean, and fixed them: on the same programs the geometric-mean slowdown against ELPI went from 31 times to 3, and memory from gigabytes to about 100 MB. See [Why LeanElpi was 30 times slower, and what fixed it](/blog/why-leanelpi-was-slow/). The compatibility results below are unchanged. A later article, [Every ELPI performance program now runs on LeanElpi](/blog/every-performance-program-runs/), closed the language gaps behind the programs that were rejected here: none of the 24 benchmark programs is rejected now, and the upstream suite passes 52 of 114 tests instead of 43.

LeanElpi is a clean-room implementation of the ELPI dialect of λProlog. Two questions decide whether you can use it in place of the original: does it accept and run your programs, and how long do they take? We measured both for release 0.3.0, against ELPI 1.18.2 (the OCaml original) and, for speed, against Teyjus 2.1.1, the other well-known λProlog system. The short answer is that compatibility is partial and performance is not yet competitive. The numbers follow, with the commands to reproduce them.

## How we tested

**Compatibility** is judged by two suites, both run with the real ELPI as the oracle.

- The **conformance corpus** has 40 programs of our own. Each runs under ELPI and under LeanElpi, and standard output and exit status must be identical.
- The **upstream suite** is ELPI's own test registry, copied from the 1.18 sources: 159 entries, each judged by upstream's rule (exit status 0 is success, unless the registry expects a failure or an output pattern). We run the real ELPI on it first, so a failure in the harness or in our copy shows up before we blame LeanElpi.

**Performance** uses the `performance_FO` and `performance_HO` programs from that same registry (queens, zebra, crypt, the `mu` puzzle, list and map workloads, call-by-value and call-by-name reduction, and more), plus three small programs of ours that finish on every engine. Each program runs three times; we report the median wall time and the peak resident memory. Failures are recorded as failures, never as times. All engines run with the same 64 MB stack limit, the largest macOS allows, because two upstream programs recurse deeply.

The machine was an Apple M2 Max with 64 GB of RAM, macOS, one program at a time. ELPI 1.18.2 came from opam on OCaml 4.14.2. Teyjus 2.1.1 was built from its git repository (it needs OCaml below 5.0). Teyjus runs only the programs that are also valid Teyjus modules (`.mod` plus `.sig`), which is six of them. LeanElpi was the 0.3.0 build from commit `e45a283`.

## Compatibility results

| Suite | Result |
|---|---|
| ELPI 1.18.2 on the upstream suite (harness check) | 114 of 114 pass, 45 skipped |
| LeanElpi on the upstream suite | 43 of 114 pass, 71 registered known failures, 0 unexplained failures |
| Conformance corpus, LeanElpi against ELPI | 38 of 40 identical, 2 registered divergences |

Of the 159 upstream entries, 45 are skipped for every engine: 23 are performance programs (timed below instead), 14 compare ELPI's JSON trace format, 7 need the legacy parser and one needs a large corpus that is not vendored. That leaves 114 tests. ELPI passes all of them, which shows the harness is sound. LeanElpi passes 43, or 38%.

The 71 failures are not hidden. Each one is registered in `tests/upstream/known-failures.md` with the first error LeanElpi reports, and the runner counts it as known rather than passing. Grouped by that first error:

| First error | Tests | What it means |
|---|---|---|
| Type checker or type abbreviations | 18 | The checker rejects programs ELPI accepts: abbreviations, `pi` and `=>` applied to more arguments than their type allows, unknown types |
| Parse error | 16 | Syntax LeanElpi does not read yet: notation declarations, backquote and quote syntax, some operators and index annotations |
| Undeclared constant | 17 | A builtin is missing (`random.int`, `same_var`, `print_constraints`) or scoping differs (namespaces, implicit binders) |
| Unsupported directive | 11 | `macro`, `mode` inside CHR blocks and `shorten` are not implemented |
| Unknown command-line option | 7 | Flags such as `-no-tc` and `-delay-problems-outside-pattern-fragment` |
| Runs, but the query fails | 2 | A real behavioural difference |

The grouping is by the first error message, so it is a guide and not a diagnosis: one missing feature can surface under another heading.

The two divergences in the conformance corpus go the other way. In both, ELPI aborts or answers differently on a problem outside the higher-order pattern fragment, and LeanElpi follows its own specification instead, suspending the problem as a delayed goal. They are registered in `tests/conformance/divergences.md` as debt against the requirement text, not as accepted differences.

What the numbers say: the core language mostly works. Plain clauses, backtracking, `pi` and `=>`, higher-order pattern unification and much of the standard library pass. The gaps are at the edges: syntax extensions, the type checker's corner cases and the less common builtins. If your program uses plain λProlog you have a good chance. If it uses ELPI's more advanced features, run it through `lean-elpi` and check.

## Performance results

Median wall time of three runs, in seconds. A dash means the engine does not run that program; "rejected" means LeanElpi stops with a parse, type or builtin error (a compatibility failure, not a speed result).

| Program | ELPI 1.18 | LeanElpi 0.3.0 | Teyjus 2.1.1 | LeanElpi / ELPI |
|---|---|---|---|---|
| fib 23 (ours) | 0.125 | 0.512 | – | 4× |
| crypt | 2.09 | 44.8 | 4.06 | 21× |
| fast_mu | 0.86 | 13.7 | 1.81 | 16× |
| mu | 1.18 | 35.9 | 3.26 | 30× |
| nrev, 400 elements (ours) | 0.151 | 7.53 | – | 50× |
| church numerals, 5 applied to 5 (ours) | 0.085 | 2.85 | – | 33× |
| queens | 0.94 | 66.5 | 1.29 | 70× |
| cbv (call-by-value reduction) | 1.62 | 64.7 | – | 40× |
| cbn (call-by-name reduction) | 0.24 | 33.7 | – | 142× |
| zebra | 0.60 | rejected | 1.36 | – |
| rev14 | 0.17 | out of memory | 0.08 | – |
| rev | 0.16 | out of memory | – | – |
| lambda3 | 0.27 | timeout (300 s) | – | – |

Startup for a trivial program is 35 ms for LeanElpi and 67 ms for ELPI. `ackermann` is too small to tell apart: both engines finish it at startup cost.

Ten further performance programs (`index2`, `deep_index`, the three `map` variants, `map_ho`, `set`, `set_ho`, `dt`, `dt_off`) are rejected by LeanElpi before they run: they use `macro`, indexing annotations or the `std.map` and `std.set` modules. With `zebra`, that is 11 of the 21 performance programs we could run. They count against compatibility, and they mean the speed table covers only the programs LeanElpi can already read.

### What the speed numbers say

- **On the eight programs where both engines finish and ELPI needs more than 0.1 s, LeanElpi is 4 to 142 times slower than ELPI, 31 times slower by geometric mean.** The design paper had predicted 3 to 10 times. That prediction was wrong, and we have corrected it in the design paper. The best case (`fib`) matches it; the typical case does not.
- **Teyjus is between ELPI's speed and 3 times slower on these programs**, except `rev14`, where its compiled abstract machine finishes in 79 ms, twice as fast as ELPI. ELPI is faster than Teyjus on queens, zebra, crypt, `mu` and `fast_mu` (by 1.4 to 2.8 times). So the 31 times gap is a LeanElpi problem, not a property of λProlog interpreters in general.
- **Memory is the bigger problem.** Peak resident memory for the same run:

| Program | ELPI | LeanElpi | Teyjus |
|---|---|---|---|
| queens | 134 MB | 10.5 GB | 65 MB |
| cbv | 17 MB | 15.6 GB | – |
| mu | 17 MB | 6.8 GB | 46 MB |
| nrev, 400 elements | 15 MB | 3.7 GB | – |
| rev (killed) | 44 MB | 36 GB at 90 s | – |

In these runs memory grows with the amount of work done, not with the size of the data the program holds. The two `rev` programs build a list of 160 000 elements and append it repeatedly; LeanElpi used 36 GB after 90 seconds on `rev` and the operating system ended it. This matters more than the time: a slow program finishes, a program that exhausts memory does not.

## What we make of it

LeanElpi 0.3.0 is a faithful engine for programs of moderate size, a research and teaching tool, and the host for λProlog tactics and certified search inside Lean. It is not a replacement for ELPI when speed or large inputs matter. Its design (a persistent abstract machine that stores every substitution in a persistent map) buys cheap backtracking and clean embedding in Lean. These numbers show the price.

What the data suggests is memory first: three programs exhaust it, and a program that runs out of memory gives no answer at all. After that come the optimisations the design paper already lists: a mutable store for queries that never backtrack across a Lean boundary, clause precompilation and deeper indexing. Compatibility is a separate line of work. Every fix removes an entry from `known-failures.md`, so the pass rate can be checked by anyone who runs the suite.

## Caveats

These are single-machine numbers from three runs per program, with wall-clock time and peak memory measured by the operating system. The ratio between engines is more stable than the absolute seconds. ELPI was the opam release build, Teyjus was built from git with the default flags, and neither was tuned. The three programs we wrote ourselves (`nrev`, `fib`, `hoabs`) are in `tests/bench/programs`. The copied upstream sources are LGPL-2.1.

## Reproduce it

```bash
scripts/install-oracle.sh                      # ELPI 1.18.2 in an opam switch
lake build                                     # lean-elpi

tests/upstream/run.sh oracle                   # harness check: must pass everything
tests/upstream/run.sh lean                     # the upstream suite on LeanElpi
tests/conformance/run.sh                       # our corpus, both engines

TEYJUS_BIN=/path/to/teyjus/bin python3 tests/bench/run.py --runs 3 --json out.json
```

The raw results of the run in this article are in `tests/bench/results/2026-10-15.json`. If you find a program that LeanElpi gets wrong, or a faster way to run any of the engines, please [open an issue](https://github.com/Volland/lean-elpi/issues).
