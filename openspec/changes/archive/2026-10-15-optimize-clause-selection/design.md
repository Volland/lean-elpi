## Context

The rerun of 2026-10-15 (`tests/bench/results/2026-10-15-rerun.json`) leaves these ratios against ELPI 1.18: `lambda3` 10.5, `crypt` 5.2, `mu` 5.3, `fast_mu` 4.8, `queens` 3.9, `cbn` 3.3, the rest 1.2 to 2.5; `startup` and `ackermann` run in half ELPI's time. Seven upstream workloads (`zebra`, `index2`, `deep_index`, `map_*`, `set`, `dt`) do not run, for front-end reasons (`:index(...)`, `macro`, Teyjus `nil`), not speed; they are out of scope here.

### Where the time goes

Self time from `sample` at 1 ms over 2 s of each run, as a share of the main thread:

| Workload | Hot spot | Share | Caller |
|---|---|---|---|
| `queens`, `mu` | `lean_dec_ref_cold`, `lean_alloc_small_object`, `mi_free`, `lean_del_core`, RC helpers | 40–45% | everywhere |
| `queens` | `renameCVars` (with its `Array.map`) | ~7% | `matchClause` |
| `lambda3` | `Term.shiftUp.go` (with its `Array.map`) | ~38% inclusive | `Store.deref` |
| `lambda3` | `Key` equality, `Key.compatible`, the locals loop in `callPred` | ~9% | `callPred` |
| `crypt` | `Unify.scanClean` | ~14% | `solveFlex` |
| `queens`, `mu` | `PredDB.merge`, `Array.range`, `Cand` boxes | ~2–3% | `callPred` |

`scanClean` is the occurs and scope check on a first-order binding. ELPI does the same walk (`hmove ~avoid:r`), so it is not a gap, and it is left alone.

### What ELPI 1.18 does instead

| Technique | ELPI 1.18 (`src/runtime.ml`, `src/data.ml`) | LeanElpi before this change |
|---|---|---|
| Sharing in relocation | `move` returns `t` when `delta = 0`; otherwise rebuilds a node only if a child changed (`smart_map`, `if x == x' then x`) | every node rebuilt |
| Compiled clauses | `clause = {args; hyps; vars; mode}`: head split, body a list | head and body kept as terms; `,` split at run time |
| Ready candidate lists | `get_clauses`: `Ptmap.find arg_hd arg_idx`, buckets already merged with `flex_arg_clauses` | `merge` of a bucket with the flex positions per call, then a `Cand` per clause |
| Hypotheses in the index | `=>` runs `clausify` and `add_clauses` into the program index | linear scan of all hypotheses per call |
| Trail as a pointer | checkpoint = `!T.trail`; `last_call` disables trailing | a `Store` record per attempt (kept: ~3%, see Non-goals) |

## Decisions

### D1. Sharing where the input is shared, fusion where it is fresh

`renameCVars` (instantiating a stored clause) and `Store.zonk` return the node they were given when no child changed: arrays go through `Array.mapMono`, which keeps the original array when every element is pointer-equal, and a node is rebuilt only when its head or arguments changed (`Term.sameRef`, pointer equality in compiled code, `false` in the reference implementation, so semantics never depend on it). A clause body's ground parts are therefore never copied.

The first attempt applied the same to `shiftUp`, `subst` and `substN`, and `lambda3` became 20% *slower* (3.4 s against 2.9 s, with 7.5% more instructions and twice the allocation samples). Their input is usually a term just built by the previous step and owned by nobody else, which Lean updates in place (reset/reuse); keeping the original alive for the pointer test turns that into a copy. They keep plain maps.

What `lambda3` needed instead: `Store.deref` relocated an assigned λ-term with `shiftUp` and then β-reduced it with `applyAt`, building the term twice. `Term.applyAtFrom` does both in one traversal (`substNTo` substitutes the arguments and moves the remaining binders to the target depth). `subst`, `substNTo` and `renameCVars` use it for the same shift-then-apply pattern. This alone took `lambda3` from 2.9 s to 1.5 s and from 40.5 to 23 billion instructions.

### D2. Compile clauses when they enter the database

`PredDB.push` fills two fields of `Clause`: `args`, the head's argument array, and `goals`, the body with top-level `,` split and `true` removed. The machine matches `args` and pushes one frame per goal, all with the clause's cut barrier and depth, which is exactly what splitting `,` at run time did. Fewer machine steps are taken, so a program uses less fuel; fuel is a resource bound, not an observable of a successful run.

### D3. Candidate arrays prepared at insertion

`PredDB` holds `all` (every clause in order), `flexOnly` (the clauses with a variable first argument) and `byKey`, whose bucket for a key holds the clauses with that key and the variable-headed ones, in clause order. Insertion appends to the end, so inserting a keyed clause appends to its bucket (created from `flexOnly` when new) and inserting a variable-headed clause appends to every bucket and to `flexOnly`. Load order and grafting are resolved before insertion (`graft`), so appending preserves order. A call takes `all`, a bucket or `flexOnly` as it is; the alternative on the choice stack keeps that array and an index, with no copy.

The static clauses and the hypotheses are kept apart in the alternative (`Alt.clauses` holds both arrays), so the common case, no matching hypotheses, does not build an array at all.

### D4. Hypotheses per predicate

`Locals` becomes a structure: `list` (all hypotheses, newest first, as before, for CHR and constraint snapshots), `byPred` (a persistent map from predicate to its hypotheses, newest first) and `unknown`, the hypotheses whose head was not visible when added. A call reads `byPred` for its predicate and filters by key; only when `unknown` is non-empty does it fall back to scanning `list` in order, so that order between known and unknown heads is kept.

### D5. One allocation per head-matching step

`hmatch` and `matchArgs` returned `Store × Array (Option Term) × Bool`, two pair objects per step, and bound a clause variable to `some g`, a third. They now return one `HM` record, and clause variables live in an `Array Term` where `unsetVar` (a `cvar`, which no goal term contains) marks a variable not bound yet. The per-argument closure that chose between match and unify mode became a Boolean. `queens` and `mu` lost 15% of their run time.

### D6. Unifier equations as records

The worklist held `Term × Term × Nat`, two pair objects per equation. `Eqn` is one record, and a pair whose sides are the same object is dropped before it is pushed (after D1, constants from clause bodies are often shared with the goal).

## Non-goals

- A lighter checkpoint record (ELPI's trail pointer) and `last_call`: `checkpoint`, `settle` and `undo` are about 5% of `queens` and `mu`, deferred.
- Indexing beyond the first argument and `:index(...)`: needs front-end work first.
- Hash-consing and a cached "closed" bit in `Term`: changes every pattern match on `app`.

## Risks

- **Pointer equality in pure code.** Only used to decide whether to reuse a node; the reference implementation rebuilds, so a proof about these functions sees ordinary structural code.
- **Order of candidates.** Prepared buckets must equal the old merge. `tests/Core/Index.lean` and the conformance corpus check answer order; a new test covers a variable-headed clause between keyed ones.
- **Cut in flattened bodies.** Every goal of a body carries the barrier of the call, as the split `,` did; a test cuts in the middle of a three-goal body.
