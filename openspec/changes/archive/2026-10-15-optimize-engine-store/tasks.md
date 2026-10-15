## 1. Engine

- [x] 1.1 Head matching binds clause variables (`hmatch`, `matchClause`)
- [x] 1.2 Array store with trail, checkpoint, undo, settle (`Elpi/Core/Store.lean`)
- [x] 1.3 Store beside the machine; pure attempt loops (`pickClause`, `pickTuple`)
- [x] 1.4 `inv` and `solveFlex` return the store; first-order fast path
- [x] 1.5 Hypothesis index, argument normalisation, `substN`

## 2. Verification

- [x] 2.1 Conformance corpus, upstream suite and `lake test` unchanged
- [x] 2.2 `tests/Core/Scaling.lean` guards against copies
- [x] 2.3 Benchmark re-run, results in `tests/bench/results`

## 3. Documentation

- [x] 3.1 Revise [[decisions#Persistent store]], components, the engine paper
- [x] 3.2 Blog post on what was found
