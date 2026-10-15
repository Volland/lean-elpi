## 1. Engine

- [x] 1.1 Sharing-preserving `shiftUp`, `subst`, `substN`, `renameCVars`, `zonk` (`Elpi/Core/Term.lean`, `Elpi/Core/Store.lean`)
- [x] 1.2 Compiled clauses: head argument array and flat body goals, built in `PredDB.push`
- [x] 1.3 Candidate arrays per key prepared at insertion; the machine takes them without copying
- [x] 1.4 Hypotheses indexed by predicate and key in `Locals`
- [x] 1.5 `HM` record and `unsetVar` in head matching; `Eqn` records in the unifier

## 2. Verification

- [x] 2.1 `lake test`, the conformance corpus and the upstream suite unchanged
- [x] 2.2 Tests for sharing, flattened bodies with cut, and hypotheses of other predicates
- [x] 2.3 Benchmark re-run, results in `tests/bench/results`

## 3. Documentation

- [x] 3.1 Components, engine paper (performance section), decision, changes list
- [x] 3.2 Blog post / README numbers
