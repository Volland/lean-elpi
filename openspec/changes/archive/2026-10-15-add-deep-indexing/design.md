## Context

First-argument indexing keeps one bucket per head constant of the first argument. For `f [1, 2, …, 10, N]` every clause has the head `::`, so one bucket holds them all; ELPI's discrimination trees look further down the term.

## Decisions

### D1. A filter on top of the first-argument bucket, not a trie

The candidates are the first-argument bucket (or every clause when the first argument is not indexed), filtered by the specification. A trie would answer in time proportional to the depth; the filter is linear in the bucket but each test is one hash comparison, which is enough to bring `dt` from 18 seconds to 4 (ELPI: about 1) and keeps the rest of the machine unchanged. The trie remains the next step.

### D2. The test can only remove clauses that cannot unify

`PredDB.idxMatch` rules a clause out only on a clash between rigid constants, literals or applications of constants. A clause variable, an unassigned call variable, a λ and a bound name are compatible with anything. A hash is compared only when both sides are ground to the indexed depth, and then different hashes mean a rigid clash within that depth; equal hashes only keep the clause, which unification confirms.

### D3. One specification, two places

The specification is recorded in the signature when the declaration is checked, copied to each predicate's `PredDB` and to the machine's environment, and applied to hypotheses through the hash stored in each `LocalClause` when `=>` adds it.

## Risks

- A hash collision keeps a clause that cannot unify; unification rejects it, so the result is unchanged.
- The filter is linear in the bucket: thousands of clauses with the same indexed prefix still cost a comparison each.
