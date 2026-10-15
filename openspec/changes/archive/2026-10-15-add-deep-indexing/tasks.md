## 1. Engine

- [x] 1.1 Parse `:index` before a declaration, record it in the signature
- [x] 1.2 `PredDB.spec`, `select`, `idxMatch`, `groundHash`
- [x] 1.3 Hypotheses: `LocalClause.hargs` and `ihash`, filter in `callPred`

## 2. Verification

- [x] 2.1 `tests/Core/Indexing.lean`
- [x] 2.2 Upstream suite, conformance corpus and `lake test` unchanged
- [x] 2.3 `dt` 18 s to 4 s, `index2` 47 s to 6 s
