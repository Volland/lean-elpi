## ADDED Requirements

### Requirement: Typed rule DSL
The runtime library SHALL provide the command `elpi_rules name where …` for writing ELPI rules in Lean source, against Lean types. Its body has two parts:
- Predicate signatures `pred p : T1 → … → Tn → Prop`. Each argument type `Ti` SHALL have `ToElpi`/`FromElpi` instances, for example from `deriving Elpi`.
- Clauses in ELPI syntax: `head :- body.`.

Every clause SHALL be type checked when the command is elaborated, against the declared signatures and the ELPI declarations generated for the argument types. An ill-typed clause SHALL be a Lean elaboration error at the offending token. The command SHALL produce the constant `name.compiled : Elpi.CompiledProgram`, usable with the pure, IO and typed query functions, which does no parsing at runtime. It SHALL also produce typed query helpers `name.p : T1 → … → Elpi.Query`, one per declared predicate.

#### Scenario: Ill-typed rule is rejected at compile time
- **WHEN** `inductive Node | a | b | c deriving Elpi` is in scope and `elpi_rules graph where pred edge : Node → Node → Prop; edge a "b".` is elaborated
- **THEN** elaboration fails with a type error at `"b"` saying the expected type is `node` and the actual type is `string`

#### Scenario: Rules compile to a program constant
- **WHEN** `elpi_rules graph where pred edge : Node → Node → Prop; pred path : Node → Node → Prop; edge a b. edge b c. path X Y :- edge X Y. path X Y :- edge X Z, path Z Y.` is elaborated
- **THEN** the constant `graph.compiled : Elpi.CompiledProgram` exists
- **AND** the pure typed query for `path a Y` on `graph.compiled` decodes the solutions `[Node.b, Node.c]`, in that order, without parsing any ELPI source at runtime
