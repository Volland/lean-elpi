# lean-integration Specification

## Purpose
The Coq-Elpi-style surface that runs ELPI programs inside Lean. It covers declaring programs and databases, accumulating sources, querying, ELPI-backed tactics and commands, the `lean.*` builtins that call `MetaM`, phase-restricted effects, and a programmatic `MetaM` API.

## Requirements

### Requirement: Program and database declarations
The command `elpi_program P` SHALL declare a named ELPI program, and `elpi_db D` SHALL declare a named clause database (for example `elpi_db myprog.db`). Both SHALL be stored in a Lean environment extension, so they persist in the `.olean` and are available in every module that imports the declaring module. The parsing, type checking and compilation they need SHALL be done when the declaring module is compiled, not when a downstream module uses them. A program accumulates a database with `elpi_accumulate P db D`. Clauses that a module adds to a database SHALL be visible exactly in that module and in modules that import it, never in its own imports.

#### Scenario: Program persists across imports
- **WHEN** module `A` runs `elpi_program myprog` and `elpi_accumulate myprog file "rules.elpi"`, and module `B` imports `A` and runs `#elpi myprog lp%{ main }%`
- **THEN** the query runs in `B` without `rules.elpi` being re-read or re-parsed

#### Scenario: Database extended downstream
- **WHEN** module `A` declares `elpi_db myprog.db` with the clause `known 1`, `myprog` accumulates it, and module `B` imports `A` and runs `elpi_accumulate myprog.db lp%{ known 2. }%`
- **THEN** `#elpi myprog lp%{ known X }%` in `B` has the solutions `X = 1` and `X = 2`
- **AND** the same query in `A` has only `X = 1`

### Requirement: Source accumulation
`elpi_accumulate T file "path.elpi"` SHALL add the clauses of an ELPI file to the program or database `T`, resolving the path relative to the Lean file and then through the Lake-aware library resolver. `elpi_accumulate T lp%{ … }%` SHALL add inline ELPI source. The ELPI 1.18 parser and type checker SHALL check accumulated source when it is accumulated. Every error SHALL be reported at an exact position: a position inside `path.elpi` for file sources, and, for inline sources, the Lean file position of the offending token, so the error is underlined in the editor.

#### Scenario: Inline source error maps to the Lean position
- **WHEN** a Lean file contains `elpi_accumulate myprog lp%{ p X :- undeclared X. }%` and `undeclared` has no type declaration
- **THEN** elaborating the file reports the type checker's "undeclared constant" error at the Lean line and column of `undeclared`, and the program is left unchanged

#### Scenario: File accumulation
- **WHEN** `elpi_accumulate myprog file "rules.elpi"` is elaborated, `rules.elpi` sits next to the Lean file and defines `edge a b.`
- **THEN** `#elpi myprog lp%{ edge a X }%` has the solution `X = b`
- **AND** a syntax error on line 3 of `rules.elpi` is reported as `rules.elpi:3:<col>`

### Requirement: Query command
`#elpi P lp%{ Q }%` SHALL run query `Q` against program `P` in `MetaM`. It SHALL show the solutions as an info message in the infoview: the variable bindings, with reflected terms pretty-printed as Lean syntax, followed by any residual constraints. It SHALL show the first solution by default and up to `n` solutions under `set_option elpi.solutions n`. When the query fails, or fuel runs out, `#elpi` SHALL report an error at the command, saying which of the two happened.

#### Scenario: Solutions are shown in the infoview
- **WHEN** `#elpi myprog lp%{ std.append [1] [2] L }%` is elaborated
- **THEN** the infoview shows the info message `L = [1, 2]`
- **AND** `#elpi myprog lp%{ lean.infer {{Nat.succ}} T }%` shows `T = {{Nat → Nat}}`

#### Scenario: Failure is reported
- **WHEN** `#elpi myprog lp%{ std.mem [1, 2] 3 }%` is elaborated
- **THEN** an error "query has no solution" is reported at the `#elpi` command

### Requirement: ELPI tactics
`elpi_tactic name := P` SHALL register an ELPI-backed tactic that is invoked as `by elpi name args`. Each argument SHALL be passed as an ELPI `argument`: `int N` for a numeral, `str S` for a string, `trm T` for an elaborated term. For each main goal the tactic SHALL call the ELPI entry `pred solve i:goal, i:list argument, o:list goal.` with `goal Ctx P Ty`:
- `Ctx` is the reflected local context, a list of `decl X N Ty` with `X` the `fvar` term.
- `P` is a fresh ELPI variable standing for the proof.
- `Ty` is the reflected goal type.

On success, the bridge SHALL reify `P`, turning each remaining ELPI variable into a new Lean metavariable. It SHALL check that the reified proof has the goal type with `isDefEq` and then assign the goal metavariable, and SHALL return the output goals as the new Lean goals, in order. The final proof is checked again by the kernel when the declaration is added. A failed `solve`, a failed type check or an ill-formed reification SHALL make the tactic fail with an error, leaving the goal unassigned.

#### Scenario: solve assigns the goal metavariable
- **WHEN** `P` contains `solve (goal _ Pf {{True}}) _ [] :- Pf = {{True.intro}}.` and `example : True := by elpi mytac` is elaborated
- **THEN** the goal is closed with the proof term `True.intro` and the kernel accepts the declaration

#### Scenario: Ill-typed proof is rejected
- **WHEN** `solve` binds the proof of a goal `True` to `{{(0 : Nat)}}`
- **THEN** `by elpi mytac` fails with a type mismatch error showing `Nat` and `True`, and the goal stays open

#### Scenario: Remaining goals are returned to Lean
- **WHEN** for goal `p ∧ q`, `solve` binds the proof to `{{And.intro lp:{{A}} lp:{{B}}}}` and returns `[goal Ctx A {{p}}, goal Ctx B {{q}}]`
- **THEN** after `by elpi split_tac` the Lean goals are `⊢ p` and `⊢ q`, in that order, and `all_goals assumption` closes them

### Requirement: ELPI commands and export
`elpi_command name := P` SHALL register an ELPI-backed command that runs the ELPI query `main Args` in `CommandElabM`, invoked as `elpi name args` with the same `argument` encoding as tactics. `elpi_export name` SHALL generate real Lean syntax for the command, so that afterwards `name args` parses on its own as a top-level command. Identifiers and parenthesised terms SHALL elaborate to `trm`, numerals to `int` and string literals to `str`. A command that fails SHALL report its error at the command's syntax.

#### Scenario: Exported command parses its arguments
- **WHEN** `elpi_command mycmd := myprog` and `elpi_export mycmd` are elaborated and then `mycmd Nat.succ 3 "s"` appears as a command
- **THEN** `main [trm (const "Nat.succ" []), int 3, str "s"]` runs in `CommandElabM`

### Requirement: Lean builtins
The system SHALL provide these T2 builtins, which run in the host `MetaM`:
- `lean.env.find Name Info`
- `lean.infer T Ty`
- `lean.whnf T R`
- `lean.defeq A B`
- `lean.elab Syntax ExpectedTy T`
- `lean.mk_mvar Ty M`
- `lean.pp T S`
- under commands only: `lean.add_decl Decl` and `lean.db.accumulate D Clause`

Each builtin SHALL take and return reflected terms and SHALL delegate to the corresponding Lean `MetaM` operation (`inferType`, `whnf`, `isDefEq`, the term elaborator, `mkFreshExprMVar`, `ppExpr`, `addDecl`). Every Lean state change a builtin makes, including metavariable assignments, SHALL be undone when the engine backtracks past the builtin call. An exception thrown by Lean SHALL make the builtin fail, and the exception message SHALL be available to the `lean.last-error` predicate instead of escaping the query.

#### Scenario: lean.infer returns the type
- **WHEN** the query `lean.infer {{Nat.succ}} T` runs
- **THEN** `T` is bound to `forall _ (const "Nat" []) (_\ const "Nat" [])`

#### Scenario: lean.defeq decides definitional equality
- **WHEN** the queries `lean.defeq {{2 + 2}} {{4}}` and `lean.defeq {{2}} {{3}}` run
- **THEN** the first succeeds and the second fails
- **AND** after `(lean.mk_mvar {{Nat}} M, lean.defeq M {{1}}, fail ; true)` the metavariable created in the first branch is not assigned

### Requirement: Phase-restricted effects
Every ELPI execution SHALL carry a capability flag that records whether it runs under a command, a tactic, a query or the runtime library. Builtins that change the environment (`lean.add_decl`, `lean.db.accumulate`) SHALL succeed only under commands. In any other phase they SHALL fail with an error naming the builtin and the phase, and the environment SHALL be left unchanged. The flag SHALL be fixed for the whole execution and SHALL NOT be changeable from ELPI code.

#### Scenario: Declaration added from a tactic is rejected
- **WHEN** a tactic's `solve` calls `lean.add_decl` and `by elpi bad_tac` is elaborated
- **THEN** the tactic fails with the error "lean.add_decl is only available in commands (current phase: tactic)", and no declaration is added to the environment

### Requirement: Programmatic meta API
The system SHALL provide `Elpi.query (p : Elpi.Program) (q : Elpi.Query) : MetaM (LazyList Solution)`. Here `p` is a program declared with `elpi_program` or built at runtime, and `q` is ELPI query source (with a coercion from `String`). Solutions SHALL be computed only when they are demanded. Each `Solution` SHALL expose its bindings as reflected terms decodable with `FromElpi`, together with its residual constraints. Forcing a later solution SHALL restore the `MetaM` state of the matching choice point before searching on. The phase SHALL be `query`, so environment-changing builtins are rejected.

#### Scenario: Elpi.query is usable from MetaM
- **WHEN** `#eval show MetaM _ from do let s ← Elpi.query myprog "lean.infer {{Nat.zero}} T"; return (s.head!.get? "T" : Option Expr)` is evaluated
- **THEN** it returns `some (Expr.const ``Nat [])`
- **AND** taking only the first solution of a query with infinitely many solutions terminates
