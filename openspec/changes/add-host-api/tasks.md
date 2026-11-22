## 1. Engine

- [x] 1.1 `Machine.reserve`, `Step.paused`, `totalFuel` and `refuel`; nested runs use the whole budget
- [x] 1.2 `paused` handled at every existing `Step` match
- [x] 1.3 `Scheme.varNames`; `CompiledProgram.addDeclsAt` with positioned type errors
- [x] 1.4 `PredDB.ofArray` groups keys in linear time

## 2. Host API

- [x] 2.1 `Elpi.Host` façade, `Elpi.Host.Types` and `Elpi.Host.Ast`
- [x] 2.2 `predSig?`
- [x] 2.3 `loadUnits` with located diagnostics
- [x] 2.4 `buildGoal`
- [x] 2.5 `ResultTerm`, `ofTerm`, `toJson`, `fromJson?`
- [x] 2.6 `runSlice`, `solveSliced`
- [x] 2.7 `addFacts`
- [x] 2.8 `ast`
- [x] 2.9 Host libraries for `accumulate` (`loadUnits`/`ast` with `libs`, `ast` with `view`, `accumulates`)
- [x] 2.10 `parseGoal` for goals written as text; `reservedNames`

## 3. Proofs

- [x] 3.1 `ResultTerm.json_roundtrip`
- [x] 3.2 `TyTerm.beq_iff_eq`
- [x] 3.3 `addFacts_atomic`

## 4. Tests and docs

- [x] 4.1 `tests/Host/*.lean`, one test per scenario (`Libraries.lean`, `TextGoals.lean` for 2.9 and 2.10), and the pause timing in `tests/Core/Scaling.lean`
- [x] 4.2 Component, change and decision sections in `tg.md/`; changelog entry
- [x] 4.3 Release 0.4.0 (coordinate with `add-host-callbacks`, which also targets 0.4.0; published as 0.4.1)
- [x] 4.4 Release 0.4.2 with 2.9 and 2.10
