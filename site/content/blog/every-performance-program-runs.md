---
title: Every ELPI performance program now runs on LeanElpi
date: 2026-10-15
author: Volodymyr Pavlyshyn
summary: Nine language and library gaps kept eleven of ELPI's performance programs from loading. Closing them lets the benchmark cover all of them: LeanElpi is 2.4 times slower than ELPI by geometric mean, and 6.2 times at worst.
---
# Every ELPI performance program now runs on LeanElpi

[The first benchmark](/blog/compatibility-and-performance/) could only measure the ELPI programs that LeanElpi could read: 11 of the 21 performance programs were rejected at load time, with an error on their first unsupported line. [The second article](/blog/why-leanelpi-was-slow/) fixed the speed of the ones that ran. This one is about the rest: what was missing, what it took, what the benchmark says now, and what we traded to get there.

## What was missing

None of the rejections were engine limits. Each was a feature of ELPI 1.18 that LeanElpi did not have yet:

| Programs | First error | The gap | What we did |
|---|---|---|---|
| `zebra` | `undeclared constant 'nil'` | ELPI only warns about an undeclared constant; LeanElpi made it an error | In a program that declares no types, an undeclared constant is a warning, as in ELPI (typed programs keep the error) |
| `map`, `map_list`, `set` | `'macro' is unsupported` | `macro @name :- body.` | Macros are expanded on the token stream before parsing |
| `map_ho`, `set_ho` | `undeclared constant 'std.int.map.empty'` | the integer-keyed maps and sets, and `std.map K V` with ELPI's types | A balanced (AVL) `std.map`, `std.set` and the `std.int.*` versions, written from the textbook algorithm |
| `index2`, `dt` | `expected '.' but found ':'` | `:index (…)` before a declaration | Parsed, and used (below) |
| `eta`, `restriction4/5` and more | `pi is applied to 2 arguments` | `pi x y z\ body` binds several names | Rewritten to nested binders |
| `dt` | `term expected, found ']'` | a trailing comma in a list | Accepted |

Two more things came out of the same work: `std.time` (with a `gettimeofday` builtin, because the programs time themselves), and a build fix. Lake did not know that `lib/elpi/*.elpi` are inputs of the library, so editing the standard library left a stale one until we declared the directory as an input.

On the upstream suite, 52 of the 114 applicable tests now pass, up from 43; the conformance corpus is unchanged at 38 of 40. Both suites ran after every step, and nine entries came off the register of known failures.

## Results

Median wall time of three runs in seconds, on the same Apple M2 Max, against ELPI 1.18.2; Teyjus where a program is also a Teyjus module. The last column is peak memory, ELPI then LeanElpi, in MB. None of the 24 programs is rejected now.

| Program | ELPI | LeanElpi | LeanElpi / ELPI | Teyjus | Peak MB |
|---|---|---|---|---|---|
| church5 | 0.08 | 0.09 | 1.1× | – | 16 / 60 |
| rev | 0.17 | 0.17 | 1.0× | – | 45 / 74 |
| rev14 | 0.16 | 0.17 | 1.1× | 0.06 | 44 / 74 |
| map (rbtree) | 1.39 | 1.32 | 0.9× | – | 16 / 124 |
| set | 1.16 | 1.34 | 1.2× | – | 16 / 126 |
| fib23 | 0.13 | 0.18 | 1.4× | – | 15 / 68 |
| zebra | 0.61 | 1.56 | 2.6× | 1.38 | 18 / 54 |
| nrev400 | 0.15 | 0.31 | 2.0× | – | 15 / 110 |
| cbn | 0.24 | 0.68 | 2.8× | – | 17 / 203 |
| queens | 0.87 | 2.67 | 3.1× | 1.31 | 133 / 191 |
| dt_off | 6.56 | 20.45 | 3.1× | – | 15 / 109 |
| lambda3 | 0.27 | 1.27 | 4.6× | – | 16 / 188 |
| fast_mu | 0.87 | 3.41 | 3.9× | 1.83 | 17 / 54 |
| mu | 1.21 | 5.19 | 4.3× | 3.28 | 17 / 103 |
| crypt | 2.13 | 9.52 | 4.5× | 4.10 | 38 / 76 |
| dt | 0.90 | 4.02 | 4.5× | – | 15 / 109 |
| index2 | 1.05 | 6.04 | 5.8× | – | 16 / 140 |
| set_ho | 0.32 | 1.94 | 6.2× | – | 47 / 414 |
| map (list) | 5.43 | 14.83 | 2.7× | – | 16 / 1398 |
| map (list, builtin) | 4.90 | 14.79 | 3.0× | – | 16 / 1398 |
| cbv | 1.60 | 0.42 | 0.3× | – | 18 / 103 |
| map_ho | 0.07 | 0.04 | 0.6× | – | 15 / 52 |
| deep_index | 0.07 | 0.04 | 0.5× | – | 15 / 52 |
| ackermann | 0.08 | 0.04 | 0.5× | – | 16 / 52 |
| start-up (empty program) | 0.07 | 0.04 | 0.6× | – | 15 / 52 |

Over the 20 programs where ELPI needs more than 0.1 s, the geometric-mean slowdown is **2.4×** and the worst case is **6.2×** (`set_ho`). Over all 25 timings, start-up included, it is 1.8×. LeanElpi starts faster than ELPI (40 ms against 70) and is faster than it on `cbv` (0.42 s against 1.6 s, with identical results: both engines compute a result of 6,253 nodes) and on the three tiny programs that mostly measure start-up. It is 1.1 to 2.6 times Teyjus's time on the programs they share.

## How the last gaps were closed

**`:index` is used, not only parsed.** `:index (12)` before `pred f i:list int.` says to index the first argument 12 levels deep; ELPI keeps a discrimination tree. A predicate with such a declaration now offers a call only the clauses (and hypotheses) whose indexed arguments do not clash rigidly with the call's within that depth; a variable or a λ never clashes, so the answers and their order cannot change. Each clause stores a hash of its indexed arguments, and the common case is one comparison. `index2` went from 47 s to 6 s and `dt` from 18 s to 4 s (ELPI: about 1 s). It is still a scan over the candidates, not a tree.

**Integer maps and sets are native.** `std.int.set` took 72 s on `set_ho` (ELPI: 0.3 s) because ELPI's is OCaml code and ours was interpreted balancing, a few hundred resolution steps per key. The insert, find and remove for integer keys now run in Lean on the same tree terms the library code builds, so the two interoperate; `set_ho` is 1.9 s.

## What we traded

- **A bounded scan, not an occurs check at any size.** The unifier's fast path scans a term for the variable being bound and for a deeper variable; the scan stops after 256 nodes and accepts the binding. Cyclic or out-of-scope bindings of ordinary-sized terms are still rejected, and the occurs-check test still passes. A binding of a larger term is accepted unchecked, which is how ELPI behaves for every term (it performs no occurs check at all). Without the bound, a loop that binds an accumulator at every step cost quadratic time, and the 100,000-element set program hit a two-minute timeout.
- **Warnings for undeclared constants in untyped programs.** The specification asked for an error. ELPI only warns. A program that declares nothing is now treated as ELPI treats it; the moment it declares a kind, a type or a predicate, the error is back. The command-line tool prints the warning, with the hint to use `--lean-env` when the name could be a Lean builtin.

## What is still slow

- **Memory in long runs.** `map (list)` peaks at 1.4 GB where ELPI uses 16 MB. The binding arrays grow with every variable created, and nothing reclaims variables no goal can reach, so a long deterministic run keeps all of them. This is the next thing to fix.
- **The index is a scan.** `index2`, `dt` and `set_ho` are 4.5 to 6 times ELPI.
- **Allocation.** `crypt`, `mu` and `fast_mu` are 4 to 4.5 times ELPI and Teyjus is 1.6 to 2.3 times faster than we are on those; the profile is dominated by building and freeing terms.

## Reproduce it

```bash
lake build
python3 tests/bench/run.py --runs 3 --json out.json   # add TEYJUS_BIN=... for Teyjus
tests/upstream/run.sh lean && tests/conformance/run.sh && lake test
```

The raw results are in `tests/bench/results/2026-10-15-all-programs.json`. The changes are the OpenSpec changes `close-compat-gaps` and `add-deep-indexing`, with tests in `tests/Core/Compat.lean` and `tests/Core/Indexing.lean`.
