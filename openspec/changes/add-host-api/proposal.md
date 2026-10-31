## Why

Programs that embed LeanElpi as a Lean library, such as Marien (a LadybugDB extension that runs ELPI rules over a graph), need more than text queries. They need the declared types and modes of an entry predicate before running it, solutions as terms rather than printed text, a query that pauses after a fuel slice and resumes, a way to add millions of ground facts without printing and parsing them, programs compiled from several named source units with errors located in each, and the parsed clauses for their own analyses. LeanElpi 0.3.3 has the parts, but some are internal and some are missing: `Step.outOfFuel` drops the machine, so a query cannot be resumed, and `CompiledProgram.prepare` only takes query text.

**Depends on:** `add-elpi-core` (runtime library API).

## What Changes

- A façade module `Elpi.Host` with stable types (`TyTerm`, `Arg`, `PredSig`, `GoalArg`, `ResultTerm`, `Query`, `Slice`, `Diagnostic`, `Error`, `Ast.*`) and functions (`predSig?`, `loadUnits`, `buildGoal`, `runSlice`, `solveSliced`, `addFacts`, `ast`).
- The abstract machine gains `Step.paused` and a fuel reserve, so a run can stop at a slice boundary and resume without losing the search or copying the store.
- `CompiledProgram.addDeclsAt` reports type errors with their positions; `Scheme` keeps the declared names of its type variables.
- `PredDB.ofArray` groups clauses by first-argument key in linear time (it was quadratic when many clauses share a key).
- Proofs: `TyTerm.beq_iff_eq`, `ResultTerm.json_roundtrip`, `addFacts_atomic`.

## Capabilities

### New Capabilities
- `elpi-host-api`: the host-facing Lean API.

## Impact

Existing APIs keep their behaviour: a run without slices never pauses, and every existing match on `Step` treats `paused` like `outOfFuel`. Code: `Elpi/Host.lean`, `Elpi/Host/{Types,Ast}.lean`, `Elpi/Core/Machine.lean`, `Elpi/Core/Index.lean`, `Elpi/Core/Typecheck.lean`, `Elpi/Runtime/Api.lean`. Tests: `tests/Host/*.lean`, `tests/Core/Scaling.lean`. The consumer-side contract is Marien's `engine-host-api` capability (change `add-leanelpi-host-api`).
