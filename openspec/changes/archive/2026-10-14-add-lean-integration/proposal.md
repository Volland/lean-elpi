## Why

Milestone **M3** of LeanElpi. After M1 and M2 the engine runs ELPI 1.18 programs with constraints, but it cannot yet see or build Lean terms, run as a Lean command or tactic, or call `MetaM`. That is project goal 2 and the main reason to embed ELPI in Lean at all. This change delivers the Coq-Elpi-style integration surface: the HOAS reflection of `Expr`, typed marshalling, commands and tactics backed by ELPI programs, `lean.*` builtins, a typed rule DSL for ordinary Lean programs, and the ELPI-side `lean`, `lean.ltac` and `lean.derive` libraries.

**Depends on:**
- `add-elpi-core` (M1): engine, type checker, solver registry and T2 builtins, runtime library, library resolver.
- `add-elpi-constraints` (M2): suspension of out-of-fragment problems on reflected terms, residual constraints shown with `#elpi` answers, and the T4 hooks that tactics may register.

## What Changes

- Add the HOAS `term` type, reflecting every `Lean.Expr` form: `const Name Levels`, `app Head Args`, `fun N Ty (x\ B)`, `forall N Ty (x\ B)`, `let N Ty V (x\ B)`, `sort L`, `lit L`, `mvar M`, `fvar F`, `proj S I T`, `mdata D T`. Round trips are lossless, and universe levels are opaque handles (ctype `level`) compared by identity.
- Add the marshalling classes `ToElpi`/`FromElpi` with instances for core types, and `deriving Elpi`, which emits ELPI `kind`/`type` declarations for inductives and structures.
- Add Lean term quotations inside ELPI source, `{{ fun x => x + 1 }}`, with antiquotation `lp:{{X}}` (the Coq-Elpi convention).
- Add the commands `elpi_program`, `elpi_db`, `elpi_accumulate` (from a file or inline as `lp%{ … }%`, with error positions mapped into the Lean file), `#elpi`, `elpi_tactic`, `elpi_command` and `elpi_export`. Programs and databases live in an environment extension, persist across imports and are precompiled at compile time.
- Add ELPI-backed tactics (`by elpi name args`) through the entry point `pred solve i:goal, i:list argument, o:list goal.`. Lean checks the proof term they produce (`isDefEq` against the goal type, then the kernel when the declaration is added).
- Add the `lean.*` builtins: `lean.env.find`, `lean.infer`, `lean.whnf`, `lean.defeq`, `lean.elab`, `lean.mk_mvar` and `lean.pp`. `lean.add_decl` and `lean.db.accumulate` work only under commands, a phase restriction enforced by a capability flag.
- Add `Elpi.query (p) (q) : MetaM (LazyList Solution)` for Lean metaprograms.
- Runtime library: add the typed rule DSL `elpi_rules name where …`, checked at compile time against signatures from `deriving Elpi` and compiled to a program constant.
- Libraries: add `accumulate lean` (the `term` and `goal` types, builtin signatures, helpers), `accumulate lean.ltac` (tactic combinators) and `lean.derive` (BEq, DecidableEq and Repr derivers).

## Capabilities

### New Capabilities
- `lean-reflection`: HOAS encoding of `Expr`, lossless round trip, opaque universe levels, `ToElpi`/`FromElpi`, `deriving Elpi`, quotations.
- `lean-integration`: the Lean commands, tactics, builtins, phase restriction and programmatic `MetaM` API.

### Modified Capabilities
- `elpi-runtime-library`: adds the typed rule DSL `elpi_rules` (ADDED requirement; the M1 requirements are unchanged).
- `elpi-libraries`: adds the `lean`, `lean.ltac` and `lean.derive` libraries (ADDED requirements; the M1 requirements are unchanged).

## Impact

**Motivating decisions:**
- [[decisions#Coq-Elpi style integration surface]]: the command, tactic and builtin surface and the `solve` convention.
- [[decisions#Plain types with reflected Lean terms]]: ELPI stays simply typed, `Expr` becomes HOAS data, and dependent typing is delegated to `lean.*` builtins.
- [[decisions#Lossless reflection with opaque levels]]: full `Expr` coverage and level handles.
- [[decisions#Tiered solver API]]: the `lean.*` builtins are T2 solvers running in `MetaM`.
- [[decisions#Monad-generic core and packaging]]: the core is instantiated at `MetaM`, and choice points capture `Meta.SavedState`.
- [[decisions#Persistent store]], [[decisions#Staged language surface]], [[decisions#Specs before code]].
- Rejected alternatives this design stays away from: [[alternatives#Static Lean-typed signatures only]], [[alternatives#Dependent types via CIC]].

**Constraints:**
- [[constraints#Kernel is the trust anchor]]: proofs found by ELPI are always re-checked by Lean.
- [[constraints#MetaM is not callable from C]]: the integration has to be native Lean, not FFI.
- [[constraints#CIC unification is undecidable]]: `lean.defeq` delegates to Lean's `isDefEq`, and ELPI-side unification on `term` stays syntactic and pattern-based.
- [[constraints#Lean toolchain 4.35]]: the `Expr` constructors and environment extension API are those of v4.35.0.

**Components introduced:**
- [[components#Expr reflection]] (`Elpi/Lean/Reflect.lean`)
- [[components#Marshalling]] (`Elpi/Lean/Marshal.lean`)
- [[components#Lean builtins]] (`Elpi/Lean/Builtins.lean`)
- [[components#Commands]] (`Elpi/Lean/Commands.lean`)
- [[components#Tactic bridge]] (`Elpi/Lean/Tactic.lean`)
- [[components#Rule DSL]] (`Elpi/Runtime/Dsl.lean`)
- Extended: [[components#Library resolver]] (`lean`, `lean.ltac`, `lean.derive`), [[components#Solver registry]], [[components#Runtime API]].

**Concepts:** [[glossary#HOAS]], [[glossary#Reflection]], [[glossary#Marshalling]], [[glossary#Host monad]], [[glossary#Phase restriction]], [[glossary#Builtin predicate]].

**Knowledge graph sections touched:** [[changes#add-lean-integration]], [[uml#Tactic sequence]], [[uml#Query sequence]], [[lean-together]], [[type-bridge]].

**Requirements added:**
- [[openspec:lean-reflection#HOAS term encoding]]
- [[openspec:lean-reflection#Lossless Expr round trip]]
- [[openspec:lean-reflection#Opaque universe levels]]
- [[openspec:lean-reflection#Typed marshalling classes]]
- [[openspec:lean-reflection#Deriving Elpi]]
- [[openspec:lean-reflection#Quotations]]
- [[openspec:lean-integration#Program and database declarations]]
- [[openspec:lean-integration#Source accumulation]]
- [[openspec:lean-integration#Query command]]
- [[openspec:lean-integration#ELPI tactics]]
- [[openspec:lean-integration#ELPI commands and export]]
- [[openspec:lean-integration#Lean builtins]]
- [[openspec:lean-integration#Phase-restricted effects]]
- [[openspec:lean-integration#Programmatic meta API]]
- [[openspec:elpi-runtime-library#Typed rule DSL]]
- [[openspec:elpi-libraries#Lean API library]]
- [[openspec:elpi-libraries#Tactic combinator library]]
- [[openspec:elpi-libraries#Derive library]]

**APIs and dependencies:** new Lean commands, attributes and syntax (`elpi_*`, `#elpi`, `by elpi`, `deriving Elpi`, `lp%{ … }%`), and new `.olean` environment-extension entries. Still no Mathlib dependency. Nothing breaks for M1/M2 users.
