%% tg:begin %%
# Before starting work

- Run `tg search` to find sections relevant to your task. Read them with `tg section` to understand the design intent before writing code.
- Run `tg expand` on user prompts to expand any `[[refs]]` — this resolves section names to file locations and provides context.

# Post-task checklist (REQUIRED — do not skip)

After EVERY task, before responding to the user:

- [ ] Update `tg.md/` if you added or changed any functionality, architecture, tests, or behavior
- [ ] Run `tg check` — all wiki links, code refs and annotations must pass
- [ ] Do not skip these steps. Do not consider your task done until both are complete.

---

# What is lat.md?

This project keeps a structured knowledge graph of its architecture, design decisions and test specs in the `tg.md/` directory: cross-linked markdown files describing **what** the project does and **why**. The `tg` CLI (Typed Graph) reads and checks it, and is compatible with the lat.md format. Use it to ground your work in the actual architecture rather than guessing.

# Commands

```bash
tg locate "Section Name"      # find a section by name (exact, fuzzy)
tg refs "file#Section"        # find what references a section
tg search "natural language"  # search all sections (lexical; hybrid with embeddings)
tg section "file#Section"     # read a section with its links and code references
tg expand "user prompt text"  # expand [[refs]] to resolved locations
tg cypher "MATCH (s:Section) RETURN s.section LIMIT 5"   # query the section graph
tg check                      # validate all links, code refs, indexes and annotations
tg validate --vault <dir>     # check notes against schema notes (if the project has a vault with Types/)
```

Run `tg --help` when in doubt about available commands or options.

# Syntax primer

- **Section ids**: `tg.md/path/to/file#Heading#SubHeading` — full form uses the project-root-relative path. Short form uses the bare file name when unique (e.g. `search#RAG Replay Tests`).
- **Wiki links**: `[[target]]` or `[[target|alias]]` — cross-references between sections. Can also reference source code: `[[src/foo.ts#myFunction]]`, `[[src/server.ts#App#listen]]` (class method).
- **Code refs**: `// @lat: [[section-id]]` (JS/TS/Rust/Go/C) or `# @lat: [[section-id]]` (Python) — a plain link from code to a concept.
- **Typed code edges**: `// @tg: implements:: [[auth#Login]] {since: 2}` — a labeled edge from the next declaration to a section; `-contradicts::` makes it negative; a bare `// @tg: [[x]]` equals `@lat:`.
- **OpenSpec requirements**: if the project has `openspec/`, point code at the requirement it realizes with `// @tg: implements:: [[openspec:<capability>#<Requirement>]]` and tests at the scenario they prove with `// @tg: verifies:: [[openspec:<capability>#<Requirement>#<Scenario>]]` directly above the `it(`. List the capabilities a lat.md file explains as `openspec: [capability]` in its frontmatter. `tg trace --gaps` shows what is unimplemented or unverified.

- **Ontology**: if `tg.md/code-ontology.md` exists, use its edge names (`implements`, `verifies`, `-contradicts`, ...) instead of inventing synonyms, and give a file of decisions or requirements a `type:` in its frontmatter so `tg cypher` can label it.

# Test specs

Key tests can be described as sections in `tg.md/` files (e.g. `tests.md`). Add frontmatter to require that every leaf section is referenced by an `@lat:` or `@tg:` comment in test code:

```markdown
---
lat:
  require-code-mention: true
---
# Tests

## User login

Verify credential validation and error handling for the login endpoint.

### Rejects expired tokens
Tokens past their expiry timestamp are rejected with 401, even if otherwise valid.
```

Each test references its spec with exactly one comment next to the test:

```python
# @lat: [[tests#User login#Rejects expired tokens]]
def test_rejects_expired_tokens():
    ...
```

`tg check` flags any spec section not covered by a code reference, and any reference to a nonexistent section.

# Section structure

Every section in `tg.md/` **must** have a leading paragraph — at least one sentence right after the heading, before any child heading. The first paragraph must be ≤250 characters (excluding `[[wiki link]]` content). It is the section's overview and is used in search results and command output.
%% tg:end %%
