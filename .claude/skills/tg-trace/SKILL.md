---
name: tg-trace
description: Trace OpenSpec requirements to the code that implements them, the tests that verify their scenarios and the lat.md docs that explain them, with tg. Use when implementing or testing a requirement, when a project has an openspec/ folder, before archiving an OpenSpec change, or when asked what is implemented, tested or covered.
---

# Requirement traceability with tg

`tg` reads `openspec/specs/<capability>/spec.md` and the spec deltas of open changes. Every requirement and scenario has an id, code and tests point at those ids in comments, and `tg trace` reports what is implemented, verified and documented.

## Ids

```
openspec:<capability>#<Requirement>
openspec:<capability>#<Requirement>#<Scenario>
```

- `<capability>` is the folder name under `openspec/specs/`. `<Requirement>` is the text after `### Requirement:`; `<Scenario>` the text after `#### Scenario:`.
- Matching ignores case and collapses whitespace. A typo fails `tg check` with a did-you-mean suggestion.
- Requirements ADDED or MODIFIED in an open change resolve at once, shown as `pending in <change>`. Archiving keeps the id.

## Link code, tests and docs

Put one comment line directly above the declaration that realizes a requirement. Annotate the entry points (one to three symbols), not every helper:

```ts
// @tg: implements:: [[openspec:auth#Token expiry]]
export function checkToken(token: Token): Result {
```

Put one line per scenario directly above the test call that proves it. It attaches to the test and records its name; keep any `@lat:` line for the test spec next to it:

```ts
// @lat: [[tests/auth#Expired token]]
// @tg: verifies:: [[openspec:auth#Token expiry#Expired token]]
it('rejects an expired token with 401', () => {
```

Several edges fit on one line: `// @tg: verifies:: [[openspec:a#X#S1]], verifies:: [[openspec:a#X#S2]]`. Python and shell use `#` comments, SQL `--`.

Name the capabilities a lat.md file explains in its frontmatter (lat.md ignores the key):

```yaml
---
openspec: [auth, "billing#Refunds"]
---
```

## Check and report

```bash
tg check                       # broken openspec: targets and frontmatter entries fail here
tg trace                       # every capability: implements, verifies, docs per requirement
tg trace auth billing --gaps   # only requirements still unimplemented or unverified
tg trace --json                # for scripts
tg trace --strict              # exit 1 while any gap remains (CI, once coverage is complete)
tg edges --type verifies --to "openspec:auth#Token expiry"
```

A requirement is **implemented** when an `implements` edge reaches it or one of its scenarios, **verified** when every scenario has a `verifies` edge (or, with no scenarios, the requirement has one), and **documented** when a lat.md file names it. Missing links never fail `tg check`; only `tg trace --strict` enforces coverage.

## Rules that keep links working

- **Never rename a requirement or scenario that code points at.** Rewrite its sentence instead. If a rename is unavoidable, update every annotation in the same change: `tg edges --to "openspec:<cap>#<Old name>"` lists them, and `tg check` catches the rest.
- **Write the annotation with the code**, in the same edit, not afterwards.
- **A requirement with no test is a finding, not a failure.** Report it; do not invent a test name to silence it.
- **Negative edges** (`-implements::`) are ignored by the trace. Use `-contradicts::` for code that knowingly breaks a requirement, with `{until, ticket}`.

## Graph

The same links are graph data: `Requirement` and `Scenario` nodes joined by `contains`, reached by `implements`, `verifies` and `references`. See the `tg-graph` and `tg-impact` skills for queries.
