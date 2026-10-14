---
name: tg-graph
description: Query the lat.md section graph with openCypher through tg. Use when you need relationships between sections, such as what links to what, what is nested where, or which sections nothing references.
---

# Querying the section graph

`tg cypher "<query>"` runs read-only openCypher over the documentation graph. The same query is available to MCP clients as the `tg_cypher` tool.

## Model

- Nodes: label `Section` (plus the file's `type:` frontmatter, e.g. `Decision` or `Requirement`, on sections below the title), properties `section` (the lat id), `title`, `file`, `depth`, `startLine`, `endLine`, `summary`.
- Edges: `contains` (parent section to child section) and `references` (a wiki link that resolves to a section).
- Edge properties: `r.sign` (+1 or -1) and `r.id`.
- With an `openspec/` folder: `Requirement` nodes (`requirement` id, `capability`, `name`, `text`, `file`, `line`, `status` active or pending, `change`) and `Scenario` nodes (`scenario` id, `requirement`, `name`), joined by `contains`. A lat.md file's `openspec:` frontmatter adds `references` from its root section to each requirement it names.
- With `--code annotated` or `all`: `CodeFile` and `CodeSymbol` nodes (`path`, `symbol`, `kind`, `lang`, `startLine`), and `@tg:` annotations as edges of their own type (`implements`, `verifies`, ...) to sections, requirements or scenarios; a test's annotation starts at its file and carries `test`.

## Examples

```cypher
// Sections nothing links to
MATCH (s:Section) OPTIONAL MATCH (a)-[r:references]->(s) WITH s, count(r) AS n WHERE n = 0 RETURN s.section LIMIT 20

// Who references the Packaging section
MATCH (a:Section)-[:references]->(b:Section {title: "Packaging"}) RETURN a.section, b.file

// Biggest hubs
MATCH (s:Section)<-[r:references]-() RETURN s.section, count(r) AS n ORDER BY n DESC LIMIT 10
```

## Ontology queries

With the vocabulary in `tg.md/code-ontology.md` and `tg cypher --code annotated`:

```cypher
// Requirements nothing implements
MATCH (s:Requirement) OPTIONAL MATCH (c)-[r:implements]->(s) WITH s, count(r) AS n WHERE n = 0 RETURN s.section

// Knowing contradictions, with their expiry
MATCH (c)-[r:contradicts]->(d) RETURN c.symbol, d.section, r.until, r.ticket
```

## Requirement queries

```cypher
// Requirements of one capability with how many symbols implement each
MATCH (r:Requirement {capability: "auth"}) OPTIONAL MATCH (c)-[i:implements]->(r) RETURN r.name, count(i) AS impl

// Scenarios nothing verifies
MATCH (s:Scenario) OPTIONAL MATCH (t)-[v:verifies]->(s) WITH s, count(v) AS n WHERE n = 0 RETURN s.scenario

// Requirements pending in an open change
MATCH (r:Requirement {status: "pending"}) RETURN r.change, r.requirement
```

`tg trace` gives the same picture as a report; the `tg-impact` skill has queries for a planned code change.

## Typed code edges

`tg edges --type implements` lists `@tg:` annotation edges (code to section) with their properties, signs and sources.

## Limits

Supported: MATCH, OPTIONAL MATCH, WITH, RETURN, ORDER BY, SKIP, LIMIT, aggregation and variable-length paths. Write clauses are rejected. Pattern predicates such as `WHERE NOT ()-[:x]->(s)`, list comprehensions, map projections and `EXISTS {}` or `COUNT {}` subqueries are reported as unsupported by name: use OPTIONAL MATCH with a count instead.
