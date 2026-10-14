## Why

ELPI's core is simply typed. To reason about typed things, such as type systems or operational semantics, a program currently checks well-formedness itself, and nothing certifies an answer. Lean, by contrast, has a small trusted kernel that can certify proofs but no logic-programming search. This change adds LF (the Edinburgh Logical Framework, λΠ) as an opt-in dependent layer on the same engine, Twelf-style. LF signatures then gain judgments-as-types checking, every successful LF query yields a proof term, and the proof term becomes a theorem about a Lean inductive family that the Lean kernel checks.

The timing follows from the milestones. Pattern unification ([[constraints#Pattern unification is decidable]]) and the persistent store from M1, the unification hooks from M2, and Expr construction and kernel access from M3 are exactly the parts LF certification needs. The extension adds a checker, a recorder, an exporter and a strategy layer on top of them, and leaves the core engine unchanged.

**Milestone:** LF (the dependent extension), status **proposed**.
**Depends on:** `add-elpi-core` (M1: term store, pattern unifier, abstract machine, persistent store), `add-elpi-constraints` (M2: delayed goals and the unification-hook tier, used by the defeq bridge), and `add-lean-integration` (M3: Expr reflection, commands, MetaM access to `addDecl` and the kernel).

## What Changes

- **Per-file opt-in.** A file whose first non-comment line is `#lf` is read as an LF signature. The Lean command `lf_signature` is sugar for the same thing. Files without the header behave exactly as before.
- **LF surface syntax** that stays inside ELPI's lexical conventions:
  - declarations are written `c : A.`;
  - Π is written `pi x:A\ B`, as in ELPI's `pi x\`. Twelf's `{x:A}` is not used because braces mean spilling in ELPI;
  - `A -> B` and Twelf's `B <- A` are both type arrows;
  - free uppercase variables are implicitly Π-bound;
  - directives use `#` (`#mode`, `#block`, `#worlds`, `#total`, `#strategy`, `#bridge`) because `%` starts a comment in ELPI.
- **LF checker.** It checks the canonical λΠ typing of kinds, type families and objects, reconstructs implicit arguments and rejects ill-typed declarations with source positions.
- **Unification.** LF unification reuses the M1 higher-order pattern unifier. Implicit arguments stay explicit after erasure, and type-directed η-expansion brings objects into canonical form. Problems outside the pattern fragment are suspended, never guessed.
- **Proof-term recording.** Every LF goal carries a proof hole in the persistent store. Resolution fills the hole with the clause constant applied to its arguments, and `pi` and hypothetical goals become LF λs. Backtracking undoes partial derivations for free.
- **Export to Lean.** LF syntax families become well-scoped de Bruijn inductive types indexed by their scope (`Tm : Nat → Type`). LF judgment families become indexed inductive `Prop`s that carry an explicit context (`Of : Ctx n → Tm n → Tp → Prop`), and each constant becomes a constructor.
- **Kernel-checked certificates.** A recorded proof term is translated into a Lean `Expr` and added with `addDecl` as a theorem. Only the kernel is trusted. A corrupted proof term is rejected and adds no declaration.
- **Interoperation.** Type erasure maps an LF signature to a plain λProlog signature, so plain ELPI programs can call LF predicates. The erased program is ordinary ELPI and can also run on the 1.18 oracle.
- **Pluggable search strategy for LF only.** The strategies are depth-first (the default), bounded depth-first and iterative deepening. Plain ELPI programs keep the fixed depth-first order because their cut semantics depend on it.
- **Staged meta-theory.**
  - Twelf-style `#mode` checking comes first.
  - `#total` (worlds, coverage and termination) comes next. It reports a meta-theorem and, when it can build a proof, emits a kernel-checked Lean theorem `∀ inputs, ∃ outputs, R inputs outputs`. It never emits `sorry`.
- **Optional defeq bridge.** Through a unification hook, an LF constant can be bound to a Lean function, such as `Nat.add`, and Lean computes ground applications of it. The result appears in the certificate as an index the kernel re-checks by definitional unfolding, so a faulty bridge can only produce a rejected certificate, never a false theorem.

No existing behaviour changes. Nothing here is **BREAKING**.

## Capabilities

### New Capabilities

- `elpi-lf`: an opt-in LF (λΠ) layer. It covers LF signatures and their checking, pattern unification for LF objects, proof-term recording, export of signatures to Lean inductive families, kernel-checked certificates, interoperation with plain programs, LF search strategies, mode and totality checking, and a defeq bridge to Lean computation.

### Modified Capabilities

None. The extension uses `elpi-core-engine`, `elpi-solver-api` (unification hooks) and `lean-integration` without changing their requirements.

## Impact

**Requirements added** (capability `elpi-lf`):

- [[openspec:elpi-lf#LF opt-in per file]]
- [[openspec:elpi-lf#Dependent signatures]]
- [[openspec:elpi-lf#Pattern unification for LF]]
- [[openspec:elpi-lf#Proof term recording]]
- [[openspec:elpi-lf#Lean inductive export]]
- [[openspec:elpi-lf#Kernel-checked certificates]]
- [[openspec:elpi-lf#Interoperation with plain programs]]
- [[openspec:elpi-lf#LF search strategies]]
- [[openspec:elpi-lf#Mode checking]]
- [[openspec:elpi-lf#Totality checking]]
- [[openspec:elpi-lf#Defeq bridge]]

**Decisions that motivate it:**

- [[decisions#LF as the dependent extension]] is the main decision this change carries out. Its rejected alternatives are [[alternatives#Dependent types via CIC]], [[alternatives#Static Lean-typed signatures only]] and [[alternatives#Defeq suspension as the dependent mechanism]]; the last one survives only as the optional bridge.
- [[decisions#Plain types with reflected Lean terms]] keeps the core simply typed, so LF must be a layer, not a new core.
- [[decisions#Persistent store]] gives backtracking-safe proof holes at no extra cost.
- [[decisions#Explicit abstract machine]] is the seam where the LF-only strategy plugs in.
- [[decisions#Tiered solver API]] supplies the unification-hook tier used by the defeq bridge.

**Constraints:**

- [[constraints#Pattern unification is decidable]]: LF needs no new unifier.
- [[constraints#CIC unification is undecidable]] is why CIC was rejected as the object theory.
- [[constraints#Kernel is the trust anchor]]: the engine, checker and exporter are all untrusted, and only `addDecl` acceptance counts.

**Components introduced:**

- [[components#LF checker]] (`Elpi/LF/Check.lean`): the LF parser extension, typing, reconstruction, erasure, and mode, coverage and termination checks.
- [[components#LF proof terms]] (`Elpi/LF/ProofTerm.lean`): the proof-hole elaboration, zonking and the certificate data.
- [[components#LF export]] (`Elpi/LF/Export.lean`): Lean inductive generation, the Expr translation, kernel submission and totality theorems.
- [[components#LF strategies]] (`Elpi/LF/Strategy.lean`): depth-first, bounded and iterative-deepening search.

**Components used unchanged:** [[components#Unifier]], [[components#Abstract machine]], [[components#Persistent substitution]], [[components#Parser]], [[components#Commands]], [[components#Expr reflection]] and [[components#Solver registry]].

**tg.md sections touched:**

- [[changes#add-elpi-lf]], the change record.
- [[uml#LF certification sequence]].
- The glossary entries [[glossary#LF]], [[glossary#Proof term]] and [[glossary#Certificate]].
- The paper `tg.md/papers/certified-lf.md`, with frontmatter `openspec: [elpi-lf]`.

**New Lean commands:**

- `lf_signature`
- `#lf_query`
- `lf_certify`
- `lf_export`

The CLI gains `--lf-proof`, which prints the proof terms of LF answers. There are no new external dependencies and no Mathlib.
