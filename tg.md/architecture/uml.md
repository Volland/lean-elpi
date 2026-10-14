# UML

The planned UML views of LeanElpi as Mermaid diagrams. They describe the intended design; the code skeleton follows the same module boundaries.

Each diagram names the [[components]] it involves, so a reader can jump from a box to its section and from there to the decisions behind it.

## Component diagram

The modules and their main dependencies, grouped by layer. It matches the `depends_on::` edges in [[components]].

```mermaid
flowchart LR
  subgraph Core
    Term[Term store]
    Parser
    TC[Type checker]
    Unify[Unifier]
    Store[Persistent substitution]
    Index[Clause index]
    Machine[Abstract machine]
    CStore[Constraint store]
    CHR[CHR engine]
    CB[Core builtins]
  end
  subgraph Solver
    Reg[Solver registry]
  end
  subgraph Hosts
    API[Runtime API]
    DSL[Rule DSL]
    Refl[Expr reflection]
    Marsh[Marshalling]
    LB[Lean builtins]
    Cmd[Commands]
    Tac[Tactic bridge]
    Lib[Library resolver]
    CLI
  end
  subgraph LF
    LFC[LF checker]
    LFP[LF proof terms]
    LFE[LF export]
    LFS[LF strategies]
  end
  Parser --> Term
  TC --> Parser
  Unify --> Term & Store
  Index --> Term
  Machine --> Unify & Index & Store
  CStore --> Store & Machine
  CHR --> CStore
  CB --> Machine
  Reg --> CB
  API --> Machine & TC & Reg
  DSL --> API & Marsh
  Refl --> Term
  Marsh --> Term
  LB --> Refl & Reg
  Cmd --> API & LB & Lib
  Tac --> Cmd & Refl
  Lib --> Parser
  CLI --> API & Lib
  LFC --> TC & Unify
  LFP --> Machine & LFC
  LFE --> LFP & Refl
  LFS --> Machine
```

## Core class diagram

The main types of the core and how they relate. Names are the planned Lean names; fields are abbreviated.

```mermaid
classDiagram
  class Term {
    <<inductive>>
    const(c: ConstId)
    bound(level: Nat)
    app(head: Term, args: Array Term)
    lam(body: Term)
    uvar(u: UVarId, args: Array Term)
    lit(l: Literal)
    host(d: HostData)
  }
  class UVarInfo {
    id: UVarId
    scopeLevel: Nat
    name?: String
  }
  class Clause {
    head: Term
    body: Goal
    name?: String
    nvars: Nat
  }
  class Goal {
    <<inductive>>
    atom(t: Term)
    conj / disj / pi / impl
    cut
    builtin(id, args)
  }
  class Store {
    subst: PersistentHashMap UVarId Term
    uvars: PersistentHashMap UVarId UVarInfo
    constraints: ConstraintStore
  }
  class ChoicePoint {
    goals: GoalStack
    alternatives: ClauseCursor
    store: Store
    hostState: σ
    cutBarrier: Nat
  }
  class Machine~m~ {
    goals: GoalStack
    choices: Array ChoicePoint
    program: Program
    fuel: Nat
    step() m StepResult
    solutions() LazyList Solution
  }
  class Backtrackable~m~ {
    <<class>>
    save() m σ
    restore(s: σ) m Unit
  }
  class Program {
    index: ClauseIndex
    signatures: SigTable
  }
  Machine --> Program
  Machine --> "many" ChoicePoint
  Machine ..> Backtrackable : requires instance
  ChoicePoint --> Store
  Store --> UVarInfo
  Program --> "many" Clause
  Clause --> Term
  Clause --> Goal
  Goal --> Term
```

## Machine state diagram

The states of the [[components#Abstract machine]] for one query. Backtracking always returns to the most recent choice point and restores its store and host snapshot.

```mermaid
stateDiagram-v2
  [*] --> Solve
  Solve --> SelectClause: atom goal
  Solve --> RunBuiltin: builtin goal
  Solve --> Introduce: pi or implication goal
  Solve --> Cut: cut goal
  Solve --> YieldSolution: goal stack empty
  Solve --> OutOfFuel: fuel exhausted
  Introduce --> Solve
  SelectClause --> PushChoicePoint: more candidates remain
  SelectClause --> Unify: last candidate
  SelectClause --> Backtrack: no candidate
  PushChoicePoint --> Unify
  Unify --> Solve: success, body pushed
  Unify --> Delay: stuck outside pattern fragment
  Unify --> Backtrack: clash or occurs check
  Delay --> Solve
  RunBuiltin --> Solve: success
  RunBuiltin --> Backtrack: failure
  Cut --> Solve: choice points above barrier dropped
  Backtrack --> Solve: restore newest choice point
  Backtrack --> Exhausted: no choice point left
  YieldSolution --> Backtrack: caller asks for next
  YieldSolution --> [*]: caller stops
  Exhausted --> [*]
  OutOfFuel --> [*]
```

## Query sequence

How a query flows from a caller through the core and back as a lazy stream. Under `MetaM` the builtin step reaches Lean.

```mermaid
sequenceDiagram
  actor Caller
  participant API as Runtime API
  participant M as Abstract machine
  participant I as Clause index
  participant U as Unifier
  participant S as Persistent substitution
  participant R as Solver registry
  Caller->>API: Elpi.solve program query
  API->>M: init goals, fuel
  API-->>Caller: LazyList (unevaluated)
  Caller->>API: force first solution
  loop until goal stack empty
    M->>I: candidates for atom
    I-->>M: clauses (first-argument filtered)
    M->>S: save choice point (store + host state)
    M->>U: unify head with goal
    U->>S: bind uvars (new persistent version)
    alt builtin goal
      M->>R: run builtin in host monad
      R-->>M: stream of results
    end
  end
  M-->>Caller: Solution (bindings + residual constraints)
```

## Tactic sequence

What happens for `by elpi mytac args`: the goal is reflected into ELPI, `solve` runs under `MetaM`, and the proof term comes back to Lean. See [[components#Tactic bridge]].

```mermaid
sequenceDiagram
  actor User
  participant T as TacticM
  participant B as Tactic bridge
  participant RF as Expr reflection
  participant M as Abstract machine at MetaM
  participant LB as Lean builtins
  participant K as Lean kernel
  User->>T: by elpi mytac a b
  T->>B: main goal mvar, args
  B->>RF: reflect local context and target
  RF-->>B: goal Ctx MVar Ty as ELPI term
  B->>M: query solve Goal Args NewGoals
  M->>LB: lean.infer / lean.defeq / lean.whnf
  LB-->>M: answers (MetaM state saved in choice points)
  M-->>B: first solution
  B->>RF: reify proof term and new goals
  RF-->>B: Expr
  B->>T: isDefEq check and assign goal mvar
  T-->>User: remaining goals
  Note over T,K: When the declaration is added the kernel rechecks the whole proof
  T->>K: addDecl
```

## LF certification sequence

How an LF query becomes a kernel-checked Lean theorem. ELPI is untrusted; only the kernel decides: [[constraints#Kernel is the trust anchor]].

```mermaid
sequenceDiagram
  actor User
  participant C as LF checker
  participant M as Abstract machine (LF strategy)
  participant P as LF proof terms
  participant E as LF export
  participant K as Lean kernel
  User->>C: load #lf signature
  C->>C: check kinds, types, clauses
  C->>E: compile signature
  E->>K: add inductive families
  User->>M: LF query
  loop resolution steps
    M->>P: record constructor for clause used
  end
  M-->>P: success
  P-->>E: proof term (LF object)
  E->>E: translate to Lean Expr
  E->>K: check certificate
  K-->>User: theorem accepted, or rejection
```

## Deployment diagram

The artifacts LeanElpi produces and where each runs. The library and `.olean`s are shared by the CLI, Lean projects and user executables.

```mermaid
flowchart TB
  subgraph Build[lake build]
    LIB[LeanElpi library .olean]
    CLIEXE[lean-elpi executable]
    STDE[embedded std and lean libraries]
  end
  subgraph UserProject[User Lake project]
    REQ[require lean-elpi]
    SRC[Lean files with elpi_program, elpi_tactic]
    ELPIF[lib/elpi/*.elpi libraries]
    UEXE[executable from elpi_main]
  end
  subgraph Dev[Developer machine]
    ORACLE[elpi 1.18 oracle via opam]
    HARNESS[conformance harness]
  end
  LIB --> REQ
  REQ --> SRC
  ELPIF --> SRC
  SRC --> UEXE
  STDE --> CLIEXE
  STDE --> UEXE
  CLIEXE --> HARNESS
  ORACLE --> HARNESS
```
