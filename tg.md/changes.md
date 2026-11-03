---
type: Change
status: proposed
date: 2026-10-14
---
# Changes

The OpenSpec changes that build LeanElpi, one per milestone. Each lives in `openspec/changes/<name>/` with a proposal, design, delta specs and tasks.

Components point here with `introduced_by::` edges, so `tg cypher` can list what each milestone delivers. Run `tg trace` to see requirement coverage per capability.

## add-elpi-core

Milestone M1: the core engine, type checker, Lean builtins (T2), runtime library, standard library, CLI and the conformance suite against the oracle.

Capabilities: `elpi-core-engine`, `elpi-typechecker`, `elpi-solver-api` (builtins, registration), `elpi-runtime-library` (queries, loading, builtins), `elpi-libraries` (std, resolution, embedding), `elpi-cli`, `elpi-conformance`. Files: `openspec/changes/add-elpi-core/`.

- status:: implemented
- milestone:: M1

## add-elpi-constraints

Milestone M2: delayed goals, a backtrackable constraint store, CHR, and solver tiers T1 (CHR solvers), T3 (native handlers) and T4 (unification hooks).

Depends on [[changes#add-elpi-core]]. Capabilities: `elpi-constraints`, `elpi-solver-api` (CHR solvers, handlers, hooks). Files: `openspec/changes/add-elpi-constraints/`.

- status:: implemented
- milestone:: M2

## add-lean-integration

Milestone M3: Expr reflection, marshalling and `deriving Elpi`, quotations, commands and tactics, `lean.*` builtins, the rule DSL and the Lean-facing ELPI libraries.

Depends on [[changes#add-elpi-core]] and [[changes#add-elpi-constraints]]. Capabilities: `lean-reflection`, `lean-integration`, `elpi-runtime-library` (rule DSL), `elpi-libraries` (lean, lean.ltac, lean.derive). Files: `openspec/changes/add-lean-integration/`.

- status:: implemented
- milestone:: M3

## add-elpi-lf

The dependent extension: LF signatures opt-in per file, proof-term recording, export to Lean inductive families, kernel-checked certificates, strategies, mode and totality checking.

Depends on all three earlier changes. Capability: `elpi-lf`. Its design document is the most detailed of the four. Files: `openspec/changes/add-elpi-lf/`.

- status:: implemented
- milestone:: LF

## add-lean-interop

The type bridge: parametric and recursive `deriving Elpi`, `elpi_data`, `elpi_extern`, `#elpi_signature`, and the builtins `lean.env.indt` and `lean.add_inductive`.

Depends on [[changes#add-lean-integration]]. Capability: `lean-interop`; it also modifies `lean-reflection`. Explained in [[papers/interop]]. Files: `openspec/changes/add-lean-interop/`.

- status:: implemented
- milestone:: Interop

## add-language-bindings

The C ABI, one self-contained native library, Python, Node.js and Rust bindings, and their release to PyPI, npm and crates.io.

Depends on [[changes#add-elpi-core]]. Capability: `language-bindings`. Files: `openspec/changes/add-language-bindings/`; the release routine is `PUBLISHING.md`.

- status:: implemented
- milestone:: Bindings

## add-host-callbacks

Release 0.4.1: host predicates answered by a C callback during a query, structured answer terms, `fuelUsed`, and out-of-fuel errors that callers can tell apart; the Rust binding exposes them as `Term`, `Program::declare` and `Program::solve_host`.

Depends on [[changes#add-language-bindings]]. Capability: `language-bindings` (requirements "Host callback predicates" and "Structured answers"). Motivated by [[decisions#Synchronous host callbacks]]. Files: `openspec/changes/add-host-callbacks/`. The tag `v0.4.0` was never published (its macOS build ran on a retired runner image).

- status:: implemented
- milestone:: Bindings

## optimize-clause-selection

Compiled clauses, prepared candidate arrays, hypotheses indexed by predicate and key, fused relocation in dereferencing, and fewer per-step allocations in head matching and unification.

Follows the archived `optimize-engine-store`. Capability: `elpi-core-engine` (first-argument and hypothesis indexing, compiled clauses and term sharing). The profile analysis and the comparison with ELPI 1.18's runtime are in its design document. Motivated by [[decisions#Allocate less than OCaml]]. Files: `openspec/changes/archive/2026-10-15-optimize-clause-selection/`.

- status:: implemented
- milestone:: Performance

## add-host-api

The host-facing Lean API (`Elpi.Host`): predicate signatures, goals built from terms, structured result terms with a proved JSON round trip, resumable fuel slices, bulk facts as terms, multi-unit loading with located errors, and a public clause AST.

Depends on [[changes#add-elpi-core]]. Capability: `elpi-host-api`. Requested by Marien (its change `add-leanelpi-host-api`, capability `engine-host-api`). Files: `openspec/changes/add-host-api/`. Released in 0.4.1 together with [[changes#add-host-callbacks]]; host libraries for `accumulate`, goals parsed from text and the reserved names followed in 0.4.2.

- status:: applied
- date:: 2026-10-31
