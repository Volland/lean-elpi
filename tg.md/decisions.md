---
type: Decision
status: accepted  # per section: see each status:: line
date: 2026-10-14
owner: Volodymyr Pavlyshyn
openspec: [elpi-core-engine, elpi-typechecker, elpi-constraints, elpi-solver-api, lean-reflection, lean-integration, elpi-runtime-library, elpi-libraries, elpi-cli, elpi-conformance, elpi-lf, lean-interop, language-bindings]
---
# Decisions

The architecture decisions of LeanElpi, one section per decision, from the design interview of 2026-10-14 and the LF design. Rejected options live in [[alternatives]].

Each decision states its context, the choice and its consequences, then its `status::` (accepted) and typed edges: `motivated_by::` points at the [[constraints]], [[glossary]] concepts or earlier decisions that force it. The components each decision shapes link back from [[components]].

## Native Lean engine

LeanElpi is a clean-room λProlog engine written in Lean 4 itself, not a binding to the OCaml ELPI library and not a subprocess.

**Context.** ELPI exists as an OCaml library. Lean could link it through C FFI, talk to it over pipes, or reimplement it. Using Lean and ELPI together means ELPI predicates must call `MetaM` (type inference, definitional equality, elaboration) during search, and choice points must rewind Lean state.

**Decision.** Implement the engine natively in Lean: parser, type checker, unifier, abstract machine, constraint store. Keep the OCaml `elpi` binary only as a test [[glossary#Oracle]].

**Consequences.** One runtime and one garbage collector; builtins run in the [[glossary#Host monad]]; `lake build` produces library and binary; the engine works inside the Lean server. The cost is a large implementation and the risk of semantic drift, which [[decisions#ELPI 1.18 dialect]] and the conformance suite address.

- status:: accepted
- motivated_by:: [[constraints#MetaM is not callable from C]]
- motivated_by:: [[constraints#Upstream ELPI is LGPL]]
- motivated_by:: [[glossary#Host monad]]

## ELPI 1.18 dialect

The engine implements the language accepted by ELPI 1.18, the version of the installed oracle binary.

**Context.** ELPI 2.x and later changed the type checker and added `func` and determinacy checking. A reimplementation that targets a different dialect than its oracle cannot be differentially tested.

**Decision.** Target ELPI 1.18 syntax and semantics. Answers and their order from `elpi` 1.18 are the reference for every behaviour ELPI defines.

**Consequences.** Every conformance program is meaningful. Upgrading the dialect later is a deliberate change that bumps the oracle at the same time.

- status:: accepted
- motivated_by:: [[constraints#Oracle is ELPI 1.18]]
- motivated_by:: [[decisions#Native Lean engine]]

## Plain types with reflected Lean terms

ELPI keeps its simple type system; Lean terms appear inside ELPI as data in a HOAS `term` type, and dependent typing is checked by Lean through builtins.

**Context.** The two languages have different type systems: ELPI is simply typed with prenex polymorphism, Lean is dependently typed. Merging them would make unification undecidable.

**Decision.** Keep ELPI types plain. Reflect `Lean.Expr` as an ELPI datatype using [[glossary#HOAS]], so Lean binders become ELPI lambdas. Delegate dependent checks to `lean.infer`, `lean.defeq` and `lean.whnf`. Add typed [[glossary#Marshalling]] (`ToElpi`/`FromElpi`) and `deriving Elpi`, which emits ELPI `kind`/`type` declarations from Lean inductives.

**Consequences.** ELPI's type checker and unifier stay as upstream defines them; Lean's types stay independent and are checked only by Lean. The dependent extension is a separate, opt-in layer: [[decisions#LF as the dependent extension]].

- status:: accepted
- motivated_by:: [[constraints#Pattern unification is decidable]]
- motivated_by:: [[constraints#CIC unification is undecidable]]
- motivated_by:: [[glossary#Reflection]]

## Lossless reflection with opaque levels

Every `Lean.Expr` constructor has an ELPI counterpart and a round trip returns the identical term; universe levels travel as opaque handles.

**Context.** ELPI tactics build proof terms that Lean must accept. Any information lost in reflection (metadata, projections, levels) makes those terms differ from what Lean expects.

**Decision.** Cover `bvar` (via ELPI binders), `fvar`, `mvar`, `sort`, `const` with levels, `app`, `lam`, `forallE`, `letE`, `lit`, `mdata` and `proj`. Represent levels as opaque handles compared by identity; they are not structurally unifiable in v1.

**Consequences.** Terms produced in ELPI are accepted by Lean without repair. Universe-polymorphic reasoning inside ELPI is deferred.

- status:: accepted
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]

## LF as the dependent extension

The dependent-types layer is LF (λΠ) with Lean as metatheory: proof search in ELPI records proof terms that are exported to Lean inductive families and kernel-checked.

**Context.** Three readings of "dependent types in ELPI" were weighed: static Lean-typed signatures, defeq-suspended unification, and a full dependent logic framework. The user chose the most expressive one; the open question was its object theory.

**Decision.** Use [[glossary#LF]] as the object theory. Same engine, opt-in per file with an `#lf` header. Each successful query yields a [[glossary#Proof term]]; LF signatures compile to Lean inductive families and the proof term becomes a [[glossary#Certificate]] checked by the kernel. Mode, coverage and termination checking follow as later milestones.

**Consequences.** Unification stays in the pattern fragment, so the v1 unifier is reused. LeanElpi gains certified proof search, which neither ELPI nor Twelf offers. HOAS binders need an adequate Lean encoding because Lean inductives forbid negative occurrences.

- status:: accepted
- motivated_by:: [[constraints#Pattern unification is decidable]]
- motivated_by:: [[constraints#CIC unification is undecidable]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]

## Staged language surface

The language arrives in three milestones: M1 core λProlog, M2 constraints and CHR, M3 the Lean integration surface; some ELPI features are deferred.

**Context.** ELPI 1.18 is much larger than textbook λProlog. Implementing everything before anything runs delays the oracle feedback loop.

**Decision.** M1: hereditary Harrop goals, cut, pattern unification, load-time typing, modes, spilling, accumulate, namespaces, grafting, first-argument indexing, core builtins. M2: delayed goals and [[glossary#Constraint Handling Rules]]. M3: quotations and opaque Lean data. Deferred: `macro`, deep or multi-argument `:index`, ELPI 2.x `func`, the tracing protocol.

**Consequences.** Each milestone is one OpenSpec change ([[changes]]). Programs using deferred features are listed in the divergence register.

- status:: accepted
- motivated_by:: [[decisions#ELPI 1.18 dialect]]

## Clean-room Apache license

LeanElpi is written from papers and documentation, never from upstream source, and is licensed Apache-2.0 like Lean and Mathlib.

**Context.** Upstream ELPI is LGPL-2.1. Porting its OCaml code or vendoring its `.elpi` standard library makes LeanElpi a derivative work.

**Decision.** Clean-room implementation and a clean-room standard library with the same predicate names and behaviour. Running the LGPL binary as an external test oracle is allowed.

**Consequences.** Users can depend on LeanElpi under the same terms as Lean. Contributors must not copy upstream code.

- status:: accepted
- motivated_by:: [[constraints#Upstream ELPI is LGPL]]

## Persistent store

The substitution and constraint store are persistent data structures; a choice point keeps the old version together with the saved host-monad state.

**Context.** Backtracking must undo unification and, under `MetaM`, metavariable assignments made by Lean builtins. A mutable heap with a trail is fast but needs a trail entry for every effect.

**Decision.** Store uvar bindings in a `Lean.PersistentHashMap`. A [[glossary#Choice point]] holds the store and the `Backtrackable` snapshot of the host monad (`Meta.SavedState` under `MetaM`).

**Consequences.** Backtracking is "restore the older value" and cannot forget an effect. Expect 3–10× slower execution than OCaml ELPI until the store is optimised behind its interface.

- status:: accepted
- motivated_by:: [[decisions#Native Lean engine]]
- motivated_by:: [[glossary#Host monad]]

## Explicit abstract machine

Resolution runs as a loop over an explicit goal stack and choice-point stack with cut barriers, not as Lean recursion.

**Context.** A recursive or CPS interpreter overflows the native stack on deep searches, makes [[glossary#Cut]] awkward and cannot pause between solutions.

**Decision.** An explicit machine with [[glossary#Fuel]], lazy solution streams and fixed depth-first order for ELPI programs. A pluggable search strategy is enabled only for LF proof search. Terms use de Bruijn levels; each [[glossary#Unification variable]] records its scope level.

**Consequences.** Deep recursion is safe, queries are resumable and steppable, and answer order matches the oracle.

- status:: accepted
- motivated_by:: [[decisions#ELPI 1.18 dialect]]
- motivated_by:: [[decisions#Persistent store]]

## Tiered solver API

Users write their own solvers at four levels: CHR in ELPI, Lean builtins, native constraint handlers and unification hooks, all registered through Lean attributes.

**Context.** "Writing your own solver" ranges from a few CHR rules to a native decision procedure consulted during search.

**Decision.** T1 CHR rules in `.elpi`; T2 [[glossary#Builtin predicate]]s in Lean; T3 a [[glossary#Constraint handler]] owning a slice of the persistent constraint store; T4 a [[glossary#Unification hook]] consulted only when pattern unification is stuck. Attributes write into an environment extension, so solvers in imported modules are available everywhere.

**Consequences.** Native solvers backtrack for free because their state lives in the persistent store. Hooks cannot override a successful syntactic unification, which keeps the core sound.

- status:: accepted
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[glossary#Constraint Handling Rules]]

## Coq-Elpi style integration surface

Lean users declare programs and databases, accumulate sources, run queries, and register ELPI tactics and commands with a vocabulary modelled on Coq-Elpi.

**Context.** Coq-Elpi has validated a vocabulary for embedding ELPI in a proof assistant for years.

**Decision.** `elpi_program`, `elpi_db`, `elpi_accumulate` (file or inline), `#elpi`, `elpi_tactic` with the `solve (goal Ctx MVar Ty) Args NewGoals` convention, `elpi_command`, `elpi_export`, and the programmatic `Elpi.query`. Declarations that change the environment are allowed only in commands: a [[glossary#Phase restriction]].

**Consequences.** ELPI-written tactics and commands look native in Lean. The phase restriction mirrors Lean's own `MetaM`/`CommandElabM` split.

- status:: accepted
- motivated_by:: [[decisions#Native Lean engine]]
- motivated_by:: [[glossary#Phase restriction]]

## Monad-generic core and packaging

The core engine does not depend on `MetaM`; it is generic over a `Backtrackable` monad, which lets one engine serve the library, the CLI and Lean metaprograms.

**Context.** The CLI and ordinary Lean programs should not pay for loading a Lean environment, while metaprograms need `MetaM`.

**Decision.** Core is generic over `Backtrackable m`. Products: the runtime library (pure lazy `Elpi.solve`), the `lean-elpi` CLI with upstream-compatible flags, a REPL, precompiled executables via `elpi_main`, and ELPI-side libraries (`std`, `lean`, `lean.ltac`, `lean.derive`, `lf`) resolved through Lake. No Mathlib dependency.

**Consequences.** Queries can be pure functions. The oracle harness drives both binaries with the same command line.

- status:: accepted
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[constraints#Lean toolchain 4.35]]

## Specs before code

Requirements are written in OpenSpec and explained in tg.md before implementation; code gets `@tg: implements::` edges only when it really implements a requirement.

**Context.** The project starts from an empty repository. Stub code annotated as implementing requirements would create false edges and hide the gaps that `tg trace --gaps` reports.

**Decision.** Plan with four OpenSpec changes ([[changes]]). The Lake skeleton carries only plain `@lat:` links from modules to [[components]]. `require-code-mention` stays off until tests exist.

**Consequences.** `tg trace` shows every requirement as unimplemented at the start, which is the honest state.

- status:: accepted

## LF surface syntax

LF files use `c : A.` declarations, `pi x:A\ B` for Π, both `->` and left-associative `<-` arrows, and `#` directives, all inside ELPI's lexical conventions. Accepted with the LF change.

**Context.** Twelf writes Π as `{x:A} B` and pragmas as `%mode`, but braces mean spilling in ELPI and `%` starts a comment. ELPI's `type c A.` form cannot name Π-bound variables.

**Decision.** Adopt the syntax above, with capitalised free variables implicitly Π-bound in first-occurrence order and rule constants named like `of_lam`.

**Consequences.** One lexer serves plain and LF files. Twelf signatures need a mechanical rewrite to load.

- status:: accepted
- motivated_by:: [[decisions#LF as the dependent extension]]
- motivated_by:: [[decisions#ELPI 1.18 dialect]]

## Proof holes by elaboration

Proof terms are recorded by elaborating each LF predicate at load time into one with an extra proof argument, so the machine itself does not change. Accepted with the LF change.

**Context.** A derivation must be built during search and discarded on backtracking. A separate trace log would need its own undo, and re-running the search after success doubles the cost.

**Decision.** Each judgment `of M A` runs as `lf.of D M A`, where `D` is a proof hole bound by resolution; `pi` and `=>` add λs over the fresh variable and the hypothesis.

**Consequences.** Partial derivations live in the persistent store and backtrack for free. The plain core stays as the oracle sees it.

- status:: accepted
- motivated_by:: [[decisions#Persistent store]]
- motivated_by:: [[decisions#Explicit abstract machine]]
- motivated_by:: [[glossary#Proof term]]

## Well-scoped export with explicit contexts

LF syntax with binders is exported as Lean inductive families indexed by scope (`Tm : Nat → Type`), and hypothetical judgments take an explicit context `Ctx n` looked up through an inductive relation. Accepted with the LF change.

**Context.** Lean inductives forbid the negative occurrence in a direct HOAS encoding `lam : (Tm → Tm) → Tm`. PHOAS needs parametricity to be adequate, locally nameless adds freshness proofs to every certificate, and raw de Bruijn indices can dangle.

**Decision.** Generate `Var`, scope-indexed syntax, `Ctx` from the family's world, `Ctx.Lookup` and a `hyp` constructor per assumption. Use only fresh inductives and `Nat.succ`, with no `Fin`, numerals, instances or well-founded recursion.

**Consequences.** Certificates are checked by structural conversion alone. `examples/lf/StlcExport.lean` shows the `stlc` export and two certificates passing the kernel with no axioms.

- status:: accepted
- motivated_by:: [[decisions#LF as the dependent extension]]
- motivated_by:: [[constraints#Kernel is the trust anchor]]

## No unproved totality theorems

Totality checking emits a Lean theorem only together with a kernel-checked proof; otherwise it reports that no proof was built and adds nothing, never a `sorry`. Accepted with the LF change.

**Context.** Twelf trusts its mode, coverage and termination checkers. Turning their verdict into a Lean theorem without a proof would add an unchecked assumption to the environment.

**Decision.** Build the proof from the checked relation (by structural induction on the designated input, one case per constructor) when possible; otherwise report that no proof was built and leave the environment unchanged.

**Consequences.** Users can rely on every emitted theorem as much as on the kernel. Relations outside the supported shape (one designated argument, constructor patterns of variables, recursion on fields) pass the checker but produce no theorem.

- status:: accepted
- motivated_by:: [[constraints#Kernel is the trust anchor]]
- motivated_by:: [[decisions#LF as the dependent extension]]

## Oracle wins over spec examples

Where a scenario in the M1 specs disagrees with what the ELPI 1.18 oracle does, the implementation follows the oracle and the difference is recorded, because every requirement says the oracle is the reference.

**Context.** Black-box runs while building M1 showed three scenarios that the oracle contradicts: `std.append X Y [1, 2]` has no solutions (the first two arguments are inputs), `size "hello" N` is a type error (`size` and `substring` are functions evaluated by `is`, as are `int_to_string`, `string_to_int` and `real_to_string`), and `/` on two integers and `+` on an integer and a float are runtime errors. Warnings and type errors are printed by the oracle on standard output.

**Decision.** Follow the oracle, test the oracle's behaviour in the Lean tests (`std.appendR` provides the all-splits variant), and keep corpus programs warning-free so that output can be compared. The type-error verdict program `type-errors` is compared by exit status only. The one deliberate exception is non-pattern unification: ELPI 1.18 approximates `Y a a = g a`, while the requirement says to suspend it, so LeanElpi suspends and registers `suspended.elpi` in `tests/conformance/divergences.md`.

**Consequences.** The specs under `openspec/changes/add-elpi-core/` still contain the three stale examples; they should be corrected when the change is archived.

- status:: accepted
- motivated_by:: [[constraints#Oracle is ELPI 1.18]]

## Undeclared constants are an error only where the type is known

An undeclared constant is reported when it is used where a concrete type is expected or as the head of a goal; elsewhere it is treated as implicitly declared, as the oracle (which only warns) and the corpus require.

**Context.** The spec asks for an error on an undeclared constant, yet the oracle accepts `main :- …` and untyped data such as `p a 1.` with warnings only.

**Decision.** A constant with no declaration and no clauses is an error when the surrounding type is not a bare variable (`pred p i:int. p foo.`) or when it heads a goal (`bar X` outside the namespace that defines `foo.bar`). A predicate defined by clauses counts as declared.

**Consequences.** Programs that rely on untyped constants still load; ill-typed uses of declared predicates are rejected at load time with the position.

- status:: accepted
- motivated_by:: [[decisions#ELPI 1.18 dialect]]

## Constants are named by hash

Every non-reserved ELPI constant gets an id that is a hash of its name, so a `ConstId` means the same in every program and Lean values can be encoded without a symbol table.

**Context.** `deriving Elpi` has to build `Term`s in `ToElpi` instances, and instances are compiled once while programs intern their constants in whatever order they meet them.

**Decision.** The reserved control and reflection constants keep small fixed ids; any other name gets `1048576 + hash(name) mod 2^40`, probed to the next free id in the rare case of a collision inside one program.

**Consequences.** Compiled programs can be rebuilt from plain data without remapping, and constructors of derived types are the same constants everywhere. A collision between two names of one program is resolved by probing, so a program that mixes two colliding names is still correct.

- status:: accepted
- motivated_by:: [[decisions#Monad-generic core and packaging]]

## Goals returned to Lean share the goal's context

A tactic's returned goals are created in the local context of the goal plus the free variables their hypotheses introduce; ELPI eigenvariables cannot be returned.

**Context.** `solve` returns `list goal`, and a `goal` is a closed term; an ELPI `pi`-bound variable of a deeper scope cannot leave its scope.

**Decision.** Hypotheses introduced by `lean.ltac.intro` are fresh free variables (`lean.fresh-fvar`), the proof is built with the pseudo-constructor `lean.lam-fvar`, and the bridge reifies it with `mkLambdaFVars` so that metavariables in the body get their delayed assignments.

**Consequences.** `intro` composes with other tactics through ordinary `list goal` results. The cost is that the bridge, not ELPI, knows about the binder, which is recorded as a pseudo-constructor in `lean.elpi`.

- status:: accepted
- motivated_by:: [[constraints#Kernel is the trust anchor]]

## Two-way type bridge

Plain data types are declared once, on either side, and the other side is generated; Lean functions and inductive types cross as typed predicates and as declarations-as-data.

**Context.** [[decisions#Plain types with reflected Lean terms]] fixed that ELPI stays simply typed, but left users to write each data type twice and to hand-write untyped builtin glue. Coq-Elpi avoids the first problem by sharing the host's term language and has typed `coq.*` predicates; see [[papers/interop]].

**Decision.** `deriving Elpi` accepts type parameters and recursion, `elpi_data` defines Lean types from ELPI declarations by running the same deriving, `elpi_extern` computes an ELPI signature from a Lean function type, and `lean.env.indt` / `lean.add_inductive` make inductive declarations ELPI data. Only the plain fragment (no indices, `Type` parameters) crosses; everything else is rejected with a pointer to `Expr` reflection or LF.

**Consequences.** The ELPI text of a type has one source, so round trips are tested properties. Type variables are named by position and Lean parameter names are lost. Type classes are not bridged yet.

- status:: accepted
- motivated_by:: [[decisions#Plain types with reflected Lean terms]]
- motivated_by:: [[constraints#CIC unification is undecidable]]
- introduced_by:: [[changes#add-lean-interop]]

## Handle-and-string C ABI

Other languages reach the engine through a C interface in which programs are numeric handles and every other value is a UTF-8 string, with query answers as JSON.

**Context.** Python, Node.js and Rust programs should load a program once and query it many times, and install it with `pip`, `npm` or `cargo` on a machine without Lean. Exposing `lean_object*` would make each binding manage Lean reference counts.

**Decision.** `Elpi/Ffi.lean` keeps programs in a handle table inside the Lean runtime and exports seven C functions. `scripts/build-ffi.sh` links the engine and the Lean runtime into one shared library that depends only on system libraries. Python uses `ctypes`, Node.js uses `koffi`, Rust links the library; none needs a compiler on the user's machine except Rust's own.

**Consequences.** Each binding is a few hundred lines and needs only a JSON parser. Lean-environment builtins (`lean.*`, `elpi_extern`) are unreachable through it, and values are strings. The library is about 150 MB (44 MB compressed), because every `Lean` module is linked in, and starts in about a second. The handle table is updated atomically; a first version that read and wrote it separately gave two threads the same handle, which the Rust concurrency test caught.

- status:: accepted
- motivated_by:: [[decisions#Monad-generic core and packaging]]
- introduced_by:: [[changes#add-language-bindings]]
