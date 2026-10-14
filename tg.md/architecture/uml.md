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

The main types of the core as built in M1 (`Elpi/Core/`), and how they relate. Fields are abbreviated.

```mermaid
classDiagram
    class Term {
        <<inductive>>
        const(c: ConstId)
        bound(lvl: Nat)
        app(h: Term, args: Array Term)
        lam(body: Term)
        uvar(u: UVarId, args: Array Term)
        cvar(i: Nat, args: Array Term)
        lit(l: Literal)
        builtinData(d: Opaque)
    }
    class UVarInfo {
        level: Nat
        name?: Option String
    }
    class Clause {
        head: Term
        body: Term
        nvars: Nat
        name?: Option String
        pos: Pos
    }
    class Frame {
        goal: Term
        depth: Nat
        locals: Locals
        cutTo: Nat
    }
    class Alt {
        <<inductive>>
        frame(f: Frame)
        clauses(call: Frame, cands, next: Nat)
        stream(call: Frame, rest: LazyList)
    }
    class ChoicePoint~σ~ {
        goals: List Frame
        store: Store
        host: σ
        alt: Alt
    }
    class Machine~σ~ {
        goals: List Frame
        choices: Array ChoicePoint
        store: Store
        fuel: Nat
        resume: Bool
    }
    class Store {
        assign: PersistentHashMap UVarId Term
        info: PersistentArray UVarInfo
        delayed: List DelayedProblem
        deref(t: Term, depth: Nat) Term
    }
    class Backtrackable~m~ {
        <<typeclass>>
        save() m σ
        restore(s: σ) m Unit
    }
    class Env~m~ {
        syms: Symbols
        db: Database
        modes: HashMap Nat (Array Mode)
        builtins: HashMap Nat (Builtin m)
    }
    class Database {
        preds: PersistentHashMap ConstId PredDB
    }
    Term --> UVarInfo : uvar level lives in the store
    Clause --> Term : head and body
    Frame --> Term : goal
    Machine --> ChoicePoint : choice stack
    Machine --> Store : current substitution
    Machine --> Frame : goal stack
    ChoicePoint --> Store : snapshot
    ChoicePoint --> Alt : what to try next
    ChoicePoint ..> Backtrackable : host snapshot from save
    Machine ..> Backtrackable : requires instance
    Env --> Database : clauses, indexed by first argument
    Database --> Clause
    Store --> Term : assignments
```

## Machine state diagram

The states of the [[components#Abstract machine]] for one query (`Elpi/Core/Machine.lean`). Backtracking returns to the most recent choice point and restores its store and host snapshot.

```mermaid
stateDiagram-v2
    [*] --> Solve
    Solve --> YieldSolution: goal stack empty
    Solve --> OutOfFuel: fuel = 0
    Solve --> SelectClause: atomic goal (index lookup)
    Solve --> RunBuiltin: builtin goal
    Solve --> DrainWake: wake queue not empty (before the next goal)
    DrainWake --> Solve: woken goals pushed in wake order
    Solve --> Declare: declare_constraint
    Declare --> Solve: stored; CHR rules fired, bodies pushed
    Solve --> Solve: conjunction / pi / sigma / implication / spilled call
    Solve --> PushChoicePoint: disjunction
    Solve --> Cut: goal is !
    SelectClause --> PushChoicePoint: more than one candidate
    SelectClause --> Unify: exactly one candidate
    SelectClause --> Backtrack: no candidate
    PushChoicePoint --> Unify
    Unify --> Solve: head matches, push body goals
    Unify --> Backtrack: clash or occurs-check failure
    RunBuiltin --> Solve: success
    RunBuiltin --> Backtrack: failure
    Cut --> Solve: choice stack truncated to cut barrier
    YieldSolution --> Backtrack: next answer demanded
    YieldSolution --> [*]: consumer stops
    Backtrack --> SelectClause: restore store and host state, try next alternative
    Backtrack --> [*]: choice stack empty (exhausted)
    OutOfFuel --> [*]: resource error
```

## Query sequence

How a query flows from a caller through the core and back as a lazy stream. Under `MetaM` the builtin step reaches Lean.

```mermaid
sequenceDiagram
    participant U as Lean user code
    participant API as Elpi.Runtime.Api
    participant L as Loader (Parser, Typecheck, Index)
    participant M as Machine
    participant S as Store
    U->>API: Program.load src
    API->>L: parse, accumulate, graft, typecheck, index
    L-->>API: Except ElpiError CompiledProgram
    U->>API: solve p q
    API->>M: init goals = [q], store = empty, fuel
    M->>S: unify / assign (persistent)
    M-->>API: yield solution + resumable machine
    API-->>U: LazyList.cons sol (Thunk next)
    U->>API: force tail
    API->>M: backtrack, restore snapshot
    M-->>API: exhausted
    API-->>U: LazyList.nil
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
