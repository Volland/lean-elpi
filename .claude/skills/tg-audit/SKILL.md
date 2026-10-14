---
name: tg-audit
description: Audit OpenSpec requirements against the code that is supposed to implement them, classify every mismatch as a stale spec, a code bug or an open decision, and turn the findings into an OpenSpec change plus tg annotations. Use when asked to review, audit, align or clean up specs, when tg trace shows large gaps, or before adopting traceability in an existing project.
---

# Auditing specs against code

Specs drift. An audit reads every requirement next to the code and records what is really true, so the trace you build afterwards encodes the truth and not the drift. Never generate `implements` lines from names alone: a function called `validate` may implement half a requirement, or one the spec no longer states.

## 1. Scope

- `tg trace --json` gives every requirement with its current links. Start with capabilities that have the most gaps or the most important behavior.
- For a large project, split the capabilities into groups and audit them in parallel (one sub-agent per group), each writing structured results.

## 2. Per requirement, read the code

For each `### Requirement:` record:

| field | meaning |
|---|---|
| `status` | `implemented`, `partial`, `missing`, or `drifted` (the code does something else) |
| `code` | the implementing symbols as `path#Symbol` or `path#Class#method`, most specific first, 1 to 3 |
| `scenarios` | for each `#### Scenario:`, the test that really exercises it (`file:test name`), or none |
| `doc` | the lat.md section that explains it, if any |
| `issues` | untestable wording ("shortly", "fast"), stale names or versions, duplicates in other capabilities, missing error cases |

Verify claims by reading code and tests, not file names. Note behavior the code has that no requirement states.

## 3. Classify every mismatch

- **Stale spec**: the code is the intended behavior (tested, documented, released). Rewrite the requirement text in a MODIFIED delta.
- **Code bug**: the spec states the right behavior and the code is wrong. Keep the spec; add a task to fix the code with a test.
- **Both**: fix the wording and the code.
- **Open decision**: neither side is clearly right. Write both options down and ask; do not guess.

## 4. Write the change

Create one OpenSpec change (for example `align-specs-with-code`):

- MODIFIED requirements carry the complete requirement, header, text and every scenario. **Keep every existing requirement and scenario name**: they are ids that annotations point at. Add scenarios instead of renaming them.
- ADDED requirements for important unspecified behavior and for shipped features with no spec, with scenarios taken from tests that already exist.
- REMOVED only for requirements nothing annotates (`tg edges --to "openspec:<cap>#<name>"` is empty).
- `design.md` holds the classification table; `tasks.md` the code fixes and the open decisions.
- `openspec validate <change> --strict` must pass.

## 5. Annotate from the audit

From the recorded `code` and `scenarios`, add `// @tg: implements::` above each implementing symbol and `// @tg: verifies::` above each test (see the `tg-trace` skill). A script can insert them from structured results; insert directly above the declaration or test call, and never duplicate a line that is already there. Then:

```bash
tg check            # every new link resolves
tg trace --gaps     # what is left, honestly
```

## 6. Report

Counts by status and verdict, each code bug in one line with its location, the open decisions with both options, and the remaining gaps from `tg trace`. Gaps are information, not failure.
