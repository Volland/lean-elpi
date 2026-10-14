---
name: tg-impact
description: Find what a code change touches before making it - the OpenSpec requirements a file or symbol implements, the scenarios and tests that verify them, and the lat.md sections that explain them - then re-check after the edit. Use before modifying, refactoring, renaming or deleting code in a project that uses tg, and when asked about the blast radius of a change.
---

# Change impact with tg

Code in a tg project says which requirements it realizes. Before you change it, ask the graph what depends on it; after you change it, run exactly the tests and checks that prove those requirements still hold.

All queries below use `tg cypher --code annotated "<query>"` (also the `tg_cypher` MCP tool). They are read-only.

## 1. Before the edit: what does this code promise?

Requirements a file implements:

```cypher
MATCH (c:CodeSymbol {path: 'src/auth/token.ts'})-[:implements]->(r:Requirement)
RETURN c.symbol, r.requirement
```

For one symbol, filter on `c.symbol` (`'checkToken'`, or `'Session#refresh'` for a method).

Scenarios of a requirement and the tests that verify them:

```cypher
MATCH (r:Requirement {requirement: 'openspec:auth#Token expiry'})-[:contains]->(s:Scenario)
OPTIONAL MATCH (t)-[v:verifies]->(s)
RETURN s.name, t.path, v.test
```

A row with an empty `t.path` is a scenario nothing tests: your change is unguarded there.

The docs that explain a capability:

```cypher
MATCH (d:Section)-[:references]->(r:Requirement {capability: 'auth'})
RETURN DISTINCT d.file
```

Other code implementing the same requirement (a change here may need a matching change there):

```cypher
MATCH (c:CodeSymbol)-[:implements]->(r:Requirement {requirement: 'openspec:auth#Token expiry'})
RETURN c.path, c.symbol
```

Read the requirement text itself in `openspec/specs/<capability>/spec.md` (the `file` and `line` properties of the node point at it). If the change you were asked for contradicts it, stop and say so: either the spec changes first (an OpenSpec change) or the code change is wrong.

## 2. Make the edit

- Keep `@tg: implements::` and `@tg: verifies::` lines attached to the declaration or test they describe when you move or rename code.
- A new function that realizes a requirement gets its own `implements` line; a new test gets `verifies` for the scenario it proves.
- Deleting the last implementer of a requirement is a spec decision, not a refactor. Flag it.

## 3. After the edit: prove nothing broke

1. Run the tests listed in step 1, then the wider suite.
2. `tg check`: every annotation still resolves.
3. `tg trace <capability> --gaps`: nothing became unimplemented or unverified.
4. If behavior a requirement describes changed on purpose, update the spec in an OpenSpec change and the lat.md section from step 1.

## Hot spots

Files that carry the most requirements are where an edit is most likely to change what the product promises:

```cypher
MATCH (c:CodeSymbol)-[:implements]->(r:Requirement)
RETURN c.path AS file, count(DISTINCT r) AS reqs ORDER BY reqs DESC LIMIT 10
```

## Limits

The built-in engine has no pattern predicates (`WHERE NOT ()-[:x]->(n)`) or list comprehensions; use `OPTIONAL MATCH` with `count`. Test annotations attach to the test file, so `t.path` is the file and `v.test` the test name.
