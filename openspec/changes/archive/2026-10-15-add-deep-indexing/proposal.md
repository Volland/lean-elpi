## Why

ELPI lets a predicate declare how deeply, and on which arguments, its clauses are indexed: `:index (12)` before `pred f i:list int.`, or `:index (_ _ _ _ _ _ _ _ 1)` to index the ninth argument. Without it, three ELPI performance programs (`dt`, `dt_off`, `index2`) tried every clause whose first argument had the same head, which for lists means all of them: 18 and 47 seconds against about one second for ELPI.

**Depends on:** `close-compat-gaps` (archived), which made the attribute parse.

## What Changes

- `:index (d1 … dn)` before a `pred` declaration is kept as the predicate's **index specification** (depth per argument, `_` for not indexed) and applies to its program clauses and to its hypotheses.
- A call is offered the clauses whose indexed arguments are not rigidly incompatible with the call's, down to the given depth. Clause variables, unassigned variables and λ-terms always stay compatible, so the specification never removes a clause that could unify: it only changes how many are tried.
- To make the filter cheap, each clause stores a hash of every indexed argument (when ground to the indexed depth); a call's hash is compared with it before any structure is compared.

## Capabilities

### Modified Capabilities
- `elpi-core-engine`: a new requirement, "Deep and multi-argument indexing".

## Impact

**Components changed:** [[components#Clause index]], [[components#Abstract machine]], [[components#Parser]].
