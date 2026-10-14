# Contributing

## Clean-room policy

Upstream ELPI is LGPL-2.1; LeanElpi is Apache-2.0 and is a clean-room implementation
(`tg.md/decisions.md#Clean-room Apache license`). Contributors **must not read or copy the
upstream ELPI sources** (`elpi` on opam, `LPCIC/elpi` on GitHub, including its `*.elpi`
standard library and its test suite). Behaviour is taken from:

- the ELPI documentation and the published papers,
- black-box runs of the installed oracle (`elpi -test`, `elpi -parse-term`, `-print-ast`),
  never its source code, and
- the specs in `openspec/`.

The conformance corpus (`tests/conformance/corpus/`) is written by this project, not copied
from upstream. When the oracle's behaviour differs from a spec, record the decision in
`tests/conformance/divergences.md` and fix the spec in a change.

## Workflow

- Specs first: requirements live in `openspec/`, explained in `tg.md/`; code gets
  `-- @tg: implements:: [[openspec:…]]` edges and tests get `-- @tg: verifies:: [[…]]`.
- `lake build && lake test && lake run conformance` must pass; run `tg check` and
  `tg trace <capability> --gaps` before finishing a change.
- `scripts/check-core-imports.sh` keeps `Elpi/Core` free of `Lean.Meta`/`Lean.Elab`.
