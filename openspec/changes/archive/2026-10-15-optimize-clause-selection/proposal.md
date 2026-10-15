## Why

After `optimize-engine-store` the engine is 1.2 to 10.5 times slower than ELPI 1.18 on the benchmark programs it runs (3 by geometric mean). Sampling profiles of `queens`, `crypt`, `mu` and `lambda3` (`sample`, 1 ms, Apple M2 Max) show where the remaining time goes:

- **Allocation and reference counting: 40 to 45%** of `queens` and `mu` (`lean_dec_ref_cold`, `lean_alloc_small_object`, `mi_free`, `lean_del_core`). OCaml allocates in a bump-pointer minor heap and never visits dead objects; Lean frees every object through its reference count. The same allocation volume therefore costs Lean more, and the engine has to allocate *less* than ELPI to match it.
- **`Term.shiftUp` under `Store.deref`: 38% of `lambda3`.** Dereferencing an assigned variable at a deeper depth relocates its whole value, and `shiftUp` rebuilds every node even when nothing changes.
- **Scanning hypotheses: 9% of `lambda3`.** Every call walks the whole list of `=>` clauses, also for predicates that have none.
- **Per-call work that ELPI does at load time:** a fresh candidate array (`PredDB.merge`), a `Cand` box per candidate, the clause body rebuilt with its `,` spine, which then costs a machine step and two frames per conjunct.

ELPI 1.18 (`src/runtime.ml`) avoids each of these: `move` returns the original node when nothing changed (`smart_map`, `if x == x' then t`); a clause is stored as `{args; hyps; vars; mode}`; `get_clauses` returns a list prepared when the clause was added, variable-headed clauses already merged in; and `=>` adds hypotheses to the same per-predicate index (`add_clauses`).

**Depends on:** `optimize-engine-store` (archived).

## What Changes

- Term traversals (`shiftUp`, `subst`, `substN`, `renameCVars`, `Store.zonk`) keep sharing: a subterm that comes out unchanged is returned as the same object, so relocating or instantiating a term allocates only the nodes on paths that change.
- Clauses are compiled when they are added to the database: head arguments as an array and the body as a flat array of goals (top-level `,` split, `true` dropped). Selecting a clause instantiates each goal and pushes it directly.
- Each predicate keeps its candidate arrays ready: one per first-argument key, already merged with the variable-headed clauses in clause order, plus the variable-only and full lists. A call takes one of them as it is.
- Hypotheses are kept per predicate as well as in order, so a call looks only at the hypotheses for its own predicate.

## Capabilities

### Modified Capabilities
- `elpi-core-engine`: first-argument indexing and hypothesis indexing state that candidate selection does no per-call work proportional to unrelated clauses; a new requirement covers sharing in term relocation and compiled clause bodies.

## Impact

**Motivating decisions:** [[decisions#Persistent store]] (unchanged); a new decision [[decisions#Allocate less than OCaml]] records why the target is fewer allocations rather than a faster allocator.

**Components changed:** [[components#Term store]], [[components#Persistent substitution]], [[components#Abstract machine]], [[components#Clause index]], [[components#Constraint store]].
