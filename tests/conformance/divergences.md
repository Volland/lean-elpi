# Known divergences

Corpus programs where LeanElpi knowingly differs from the ELPI 1.18 oracle. Each
entry names the program, the difference, and the requirement or decision it is
debt against. The harness skips listed programs instead of failing on them.

## suspended

The oracle approximates a unification problem outside the pattern fragment
(`Y a a = g a` is solved with `Y := x\ y\ g x`, so the later `Y = x\ y\ g y`
fails and `main` exits with status 1). LeanElpi follows the requirement
`elpi-core-engine › Higher-order pattern unification`: the problem is suspended,
re-checked once `Y` is assigned, and the query succeeds. Debt against the
requirement text, which asks for both the suspension and "the oracle's answer".

## constraints-stuck_unif

Without `-delay-problems-outside-pattern-fragment` the oracle aborts with a fatal error
on `F a = g a`. LeanElpi follows the requirement `elpi-constraints › Delayed goals`
("problems outside the pattern fragment SHALL be suspended through the same mechanism")
and `elpi-core-engine › Higher-order pattern unification`: the problem becomes a
suspended goal keyed on `F` and is reported as a residual constraint.
