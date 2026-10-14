---
tgs: "0.1"
schemas:
  Decision:
    template: "[[Templates/Decision]]"
    properties:
      status: {values: [proposed, accepted, superseded, rejected], default: proposed}
      date: date
      owner: text
    edges:
      supersedes: Decision
      contradicts: [Decision, Requirement, Constraint]
      motivated_by: [Constraint, Concept, Decision]
      changed_by: Change
    visualization: {color: "#6366f1", shape: hexagon}
  Requirement:
    template: "[[Templates/Requirement]]"
    properties:
      status: {values: [draft, stable, deprecated], default: draft}
      risk: {values: [low, medium, high]}
      owner: text
    edges:
      refines: Requirement
      depends_on: Requirement
      contradicts: [Decision, Requirement, Constraint]
      introduced_by: Change
      changed_by: Change
    visualization: {color: "#0ea5e9", shape: round-rectangle}
  Scenario:
    template: "[[Templates/Scenario]]"
    properties:
      status: {values: [draft, stable, deprecated], default: draft}
    edges:
      refines: Requirement
    visualization: {color: "#14b8a6", shape: round-rectangle}
  Constraint:
    template: "[[Templates/Constraint]]"
    properties:
      source: {kind: text, required: true}
      owner: text
    edges:
      constrains: [Requirement, Decision, Component]
    visualization: {color: "#f59e0b", shape: diamond}
  Concept:
    template: "[[Templates/Concept]]"
    properties:
      status: {values: [draft, stable, deprecated], default: draft}
    edges:
      defines:
    visualization: {color: "#a855f7", shape: ellipse}
  Change:
    template: "[[Templates/Change]]"
    properties:
      status: {values: [proposed, applied, archived], default: proposed}
      date: date
    visualization: {color: "#64748b", shape: rectangle}
  Component:
    properties:
      module: text
      milestone: {values: [M1, M2, M3, LF]}
    edges:
      depends_on: Component
      motivated_by: [Decision, Constraint, Concept]
      introduced_by: Change
    visualization: {color: "#22c55e", shape: rectangle}
edgeTypes:
  implements:
    from: [CodeSymbol, CodeFile]
    to: [Requirement, Decision]
    properties:
      since: text
      confidence: {values: [full, partial]}
  verifies:
    from: [CodeSymbol, CodeFile]
    to: [Requirement, Scenario]
    properties: {since: text}
  contradicts:
    from: [CodeSymbol, CodeFile, Requirement, Decision]
    to: [Decision, Requirement, Constraint]
    properties:
      until: text
      ticket: text
    visualization: {color: "#e5484d", line: dashed}
  supersedes:
    from: Decision
    to: Decision
  motivated_by:
    from: [Decision, Component]
    to: [Constraint, Concept, Decision]
  constrains:
    from: Constraint
    to: [Requirement, Decision, Component, CodeSymbol, CodeFile]
  refines:
    from: [Requirement, Scenario]
    to: Requirement
  depends_on:
    from: [Requirement, CodeSymbol, Component]
    to: [Requirement, Component]
  defines:
    from: Concept
  introduced_by:
    to: Change
  changed_by:
    to: Change
---
# Code Ontology Schema

The Typed Graph Schema (TGS) declaration of the code ontology: seven intent types and eleven edge types, readable by the Obsidian plugin, `tg schema` and any TGS or SHACL tool.

The vocabulary and its rules of use are in `tg.md/code-ontology.md`; this note is its machine-readable form, so edit both together. It lives in `Types/`, the schema folder the Obsidian plugin, the VS Code extension and `tg validate` read by default, and outside `tg.md/` because every note directly in a schema folder declares a type. Each type's `template` links a note in `Templates/` that new notes of the type start from.

## Using it

Export it to RDF tools with `tg schema export shapes.ttl`, and check notes against it with `tg validate`. Open the project as an Obsidian vault, or use **New Typed Note** in VS Code, to create a Decision or Requirement from its template. `CodeSymbol`, `CodeFile` and `Section` are derived by `tg` and need no declaration.

## Component

`Component` was added for LeanElpi: one node per Lean module or tool in the architecture, so `tg cypher` can answer which decisions shape a module and which modules depend on it.

## Changing it

Rename, drop or add types freely: a type earns its place only when a question depends on it. Keep `tgs: "0.1"` so other readers know which version of the format this note is written for.
