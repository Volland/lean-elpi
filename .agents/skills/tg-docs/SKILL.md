---
name: tg-docs
description: Write and maintain the tg.md/ documentation folder with the tg CLI. Use when creating, editing or reviewing files in tg.md/, or when linking code to docs with @lat or @tg comments.
---

# Maintaining tg.md/ with tg

`tg.md/` is a folder of cross-linked markdown that records what the project does and why. `tg` reads, searches and checks it.

## Workflow

1. `tg search "<topic>"` then `tg section "<id>"` to read what already exists. Extend a section instead of duplicating it.
2. Edit or add markdown in `tg.md/`. Keep one idea per section.
3. Link code and docs: `[[src/file.ts#symbol]]` from docs to code, `// @lat: [[id]]` or `// @tg: implements:: [[id]]` from code to docs.
4. `tg check` until it passes.

## Rules `tg check` enforces

- Every section starts with a leading paragraph of at most 250 characters (wiki-link text not counted). It must come before any child heading.
- Every `[[link]]` resolves: to a section id, to a source file, or to a symbol (`file#Class#method`).
- Every folder has an index file named after it (`tg.md/tg.md`, `tests/tests.md`) listing its children as `- [[name]] — description`.
- Files with `require-code-mention: true` in frontmatter need an `@lat:` or `@tg:` comment in code for every leaf section.

## Section ids

`tg.md/dir/file#Heading#Sub` is the full id. `file#Heading#Sub` works when the file name is unique. Matching ignores case. A level-1 heading can be skipped: `file#Sub`.

## Typed edges in code

`// @tg: implements:: [[auth#Login]] {since: 2}` makes a labeled edge from the next declaration. Use `-type::` for a negative edge. Edge types may be restricted by a schema note's `edges` list.

OpenSpec requirements are targets too: `// @tg: implements:: [[openspec:auth#Login]]` on code, `// @tg: verifies:: [[openspec:auth#Login#Expired token]]` above a test call (it attaches to the test, with its name). `tg check` rejects a target that does not resolve and suggests the nearest one; `tg trace [capability] --gaps` lists requirements with no implementation or unverified scenarios.

## Test specs

Describe tests as leaf sections in `tg.md/tests/*.md` and put exactly one `@lat:` comment next to the test that covers each.
