## Why

The 0.3.0 benchmark (`tests/bench`, published in the blog post "How compatible and how fast is LeanElpi?") showed the engine 4 to 142 times slower than ELPI on the programs it could run, using gigabytes where ELPI uses megabytes, and running out of memory on `rev`. Profiling traced the cost to three causes, none of which is inherent in running λProlog in Lean:

- Binding a variable walked and **rebuilt the whole term** (the scope check in `inv`), so unifying a clause variable with a long list was linear in the list: appending two lists took quadratic time and memory.
- Every binding inserted into a `Lean.PersistentHashMap`, and each choice point pinned the previous version, so every binding copied a path of 32-wide nodes and freed the old one: 83% of the time on `queens`.
- Hypotheses added with `=>` were tried one by one, and goals were re-dereferenced at every step, so a program with n nested hypotheses cost n³.

**Depends on:** `add-elpi-core` (M1).

## What Changes

- Head matching binds the first occurrence of a clause variable directly to the goal's subterm (no variable, no unifier call).
- The binding store becomes arrays with an undo trail. A choice point keeps a small checkpoint instead of the whole store. The store travels beside the machine and failed attempts hand it back, so it is updated in place; this is why the matching loops are plain recursion (a `for … return` loop keeps a second reference alive and forces a copy).
- A first-order fast path in `solveFlex` assigns a term that mentions neither the variable nor a deeper variable as it is, after a read-only scan.
- Hypotheses carry their head and first-argument key, and eigenvariables are an index key; goal arguments are dereferenced once per call; β-reduction substitutes all arguments in one traversal (`substN`).
- The requirement "Persistent store" keeps its name but no longer says "no trail": the store keeps value semantics for its users, and backtracking restores it through a checkpoint.

## Capabilities

### Modified Capabilities
- `elpi-core-engine`: the store requirement (representation is free, behaviour is unchanged) and a new hypothesis-indexing requirement.

## Impact

**Motivating decisions:**
- [[decisions#Persistent store]] is revised: its consequence "3 to 10 times slower" is replaced by the measured result.

**Components changed:** [[components#Persistent substitution]], [[components#Abstract machine]], [[components#Unifier]], [[components#Clause index]].
