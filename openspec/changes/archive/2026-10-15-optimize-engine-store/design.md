## Context

The machine in `Elpi/Core/Machine.lean` kept the substitution in a persistent map and let every choice point keep the old map ([[decisions#Persistent store]]). That made backtracking trivially correct and made every effect restorable, at the price of a persistent-map update per binding. Profiling `queens`, `crypt`, `rev` and `lambda3` (see `tests/bench`) showed where the price was larger than the design paper had assumed.

## Decisions

### D1. Bind clause variables during head matching

A clause variable's first occurrence in a head is bound directly to the matching goal subterm. Unset variables become fresh unification variables only after the head has matched (`fillVars`). Anything else (a flexible goal argument, a clash with hooks present, a head variable applied to arguments) falls back to instantiating the head and unifying, so the semantics are those of the old path. A variable bound directly may be a λ used under binders, so `renameCVars` relocates it to the depth of its occurrence and β-reduces applications.

### D2. Arrays and a trail, behind the same interface

`Store.assign` and `Store.info` become arrays indexed by variable. `Store.setAssign` records the variable on `trail` when its index is below `floor`, the variable count at the newest choice point or attempt. A `checkpoint` is the store without its arrays plus the trail length; `undo` resets the trailed variables and truncates the arrays; `settle` drops the trail entries an attempt no longer needs. Everything else in the store (constraints, wake queue, names, hooks) stays persistent and is restored from the checkpoint.

A store value still behaves as a value: if a caller keeps the store it passed in, the first update copies the arrays (Lean's copy-on-write), so `unify`, `unifyMatch` and the builtin interface are unchanged.

### D3. Linear ownership in the hot path

An update is in place only when nothing else references the store. Three patterns defeat that and were each found by `dbgTraceIfShared` and the compiler's IR: a `let mut` loop with `return` keeps the previous value in its result state; a monadic continuation captures the store; a local closure captures the machine. So the store is a separate parameter of `stepM`, `callPred`, `tryClauses`, `tryStream` and `backtrack` (the `Machine.store` field is empty while the machine runs); the loops that thread it (`matchArgs`, `unifyHeadFrom`, `pickClause`, `pickTuple`, `Unify.loop`) are explicit recursion in pure code; and `inv` and `solveFlex` return the store in every case, undoing through a checkpoint when they delay.

### D4. Index hypotheses

`mkLocal` records the head predicate and the first-argument key of each hypothesis when `=>` adds it. A key for an eigenvariable (`Key.bound`) makes a goal about one name skip hypotheses about another. A `lam` or a variable stays a wildcard, because η-expansion can make a λ equal to an applied name.

## Risks

- A forgotten second reference silently turns an O(1) update into an O(n) copy. Mitigation: `tests/Core/Scaling.lean` runs a 160,000-element append and a 300-deep hypothesis chain, which are quadratic or worse if an update copies.
- `floor` only ever errs high (extra trailing), never low; the one place it is lowered is `undo`, which restores the value the checkpoint recorded.
