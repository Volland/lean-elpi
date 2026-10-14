# Code Ontology

A small shared vocabulary for what the code is meant to do: seven kinds of intent and eleven kinds of typed link between intent and code. Use these names instead of inventing synonyms, so a query means the same thing for everyone.

The machine-readable schema is `Types/code-types.md`, and `Templates/` holds a starting note for each type. Derive what the code can tell you, write what only people know, and let `tg check` and `tg cypher` tell you when the two disagree.

## Two layers

Intent is written by people and lives in `tg.md/`. Realization is the code, derived by `tg`, plus the typed links you add from code to intent.

Do not generate the intent layer from the code. A document derived from the implementation agrees with it by construction, so it can never reveal drift.

## Intent types

Mark a file with `type:` in its frontmatter and every section below its title gets that label, so `MATCH (s:Decision)` works in `tg cypher`.

- `Decision` is a choice that was made, with its reason and the alternatives rejected. An ADR is a Decision.
- `Requirement` is something the system SHALL do. One section per requirement.
- `Scenario` is a checkable example of a requirement. Test-spec sections are Scenarios.
- `Constraint` is a rule nobody here chose: a regulation, an SLA, a platform limit.
- `Concept` is a domain term with one exact meaning.
- `Change` is a unit of work that moves intent and code together, with a lifecycle.
- `Component` is a module or tool of the architecture, with `depends_on` edges to other components and `motivated_by` edges to the decisions that shape it. LeanElpi added it; see [[components]].

Files in this project: [[decisions]] and [[alternatives]] (`type: Decision`), [[constraints]] (`type: Constraint`), [[glossary]] (`type: Concept`), [[components]] (`type: Component`) and [[changes]] (`type: Change`). Requirements and Scenarios live in OpenSpec. A file may hold several types: `type: [Requirement, Scenario]`.

## Edge types

An edge says how two things relate. Write code-to-intent edges as `@tg:` comments above the declaration they describe; the edge starts at that declaration.

```
// @tg: implements:: [[requirements#Token expiry]] {since: "2.3"}
// @tg: verifies:: [[requirements#Token expiry]]
// @tg: -contradicts:: [[decisions#Stateless sessions]] {until: "2026-Q4", ticket: "PLAT-481"}
```

- `implements`: code realizes a requirement or decision. `verifies`: a test proves a requirement or scenario. When requirements live in OpenSpec, target them as `[[openspec:<capability>#<Requirement>]]` and `[[openspec:<capability>#<Requirement>#<Scenario>]]`; they appear as `Requirement` and `Scenario` nodes and `tg trace` reports coverage.
- `contradicts`: written with a minus sign, this disagrees with that, and we know it. It is how technical debt names what it is debt against.
- `supersedes`: a decision replaces an older one. `motivated_by`: the reason behind a decision.
- `constrains`: a constraint binds a requirement or code. `refines`: a more specific version of a requirement.
- `depends_on`: a dependency of intent, not an import. `defines`: where a concept gets its meaning.
- `introduced_by` and `changed_by`: provenance, pointing at a change.

Links between two sections are plain wiki links in the CLI graph (`references`), so name the relation in the sentence and keep the typed edge for code or the Obsidian plugin:

```
This replaces [[decisions#Sessions in redis]], which we dropped when the gateway took over auth.
```

## Rules of use

Short rules that keep the graph worth reading.

- **The minus sign means disagreement** and nothing else. Red dashed lines must always mean something is wrong or knowingly wrong.
- **Put facts about the relationship on the relationship:** `since`, `until`, `ticket`, `confidence: partial`.
- **A type earns its place** only if you would ask a question that depends on it. If you cannot name the query, drop the type.
- **Start small.** Five sections, three `implements`, one `verifies`, then `tg check`. If the result teaches you nothing, stop.

## Questions it answers

Run these with `tg cypher --code annotated "..."`. Replace the edge type to ask the sibling question.

```cypher
// Requirements nothing implements
MATCH (s:Requirement) OPTIONAL MATCH (c)-[r:implements]->(s) WITH s, count(r) AS n WHERE n = 0 RETURN s.section

// Built but unproven: implemented, with no test
MATCH (s:Requirement)<-[:implements]-(c) OPTIONAL MATCH (t)-[v:verifies]->(s) WITH s, count(v) AS n WHERE n = 0 RETURN DISTINCT s.section

// What we knowingly do against our own decisions
MATCH (c)-[r:contradicts]->(d) RETURN c.symbol, d.section, r.until, r.ticket

// Which components does a decision shape (section-to-section links)
MATCH (c:Component)-[:references]->(d:Decision) RETURN d.section, collect(c.section)
```

Agents can call the same queries through the `tg_cypher` MCP tool and read the typed edges instead of guessing which function is the rule and which is a workaround.

## Who uses it

Each role touches a different part of the same graph.

- **Developers** add `@tg:` edges while they work and run `tg check` before they finish.
- **Architects** own Decisions, Constraints and Concepts, and read `contradicts` and `supersedes`.
- **Product** owns Requirements and Scenarios, tags them by risk and status, and asks what is unbuilt or unproven.
- **Agents** search first, read the typed edges around the code they change, and update the sections they touched.
