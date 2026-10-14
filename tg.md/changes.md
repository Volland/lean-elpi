---
type: Change
status: proposed
date: 2026-10-14
---
# Changes

The four OpenSpec changes that build LeanElpi, one per milestone. Each lives in `openspec/changes/<name>/` with a proposal, design, delta specs and tasks.

Components point here with `introduced_by::` edges, so `tg cypher` can list what each milestone delivers. Run `tg trace` to see requirement coverage per capability.

## add-elpi-core

Milestone M1: the core engine, type checker, Lean builtins (T2), runtime library, standard library, CLI and the conformance suite against the oracle.

Capabilities: `elpi-core-engine`, `elpi-typechecker`, `elpi-solver-api` (builtins, registration), `elpi-runtime-library` (queries, loading, builtins), `elpi-libraries` (std, resolution, embedding), `elpi-cli`, `elpi-conformance`. Files: `openspec/changes/add-elpi-core/`.

- status:: implemented
- milestone:: M1

## add-elpi-constraints

Milestone M2: delayed goals, a backtrackable constraint store, CHR, and solver tiers T1 (CHR solvers), T3 (native handlers) and T4 (unification hooks).

Depends on [[changes#add-elpi-core]]. Capabilities: `elpi-constraints`, `elpi-solver-api` (CHR solvers, handlers, hooks). Files: `openspec/changes/add-elpi-constraints/`.

- status:: proposed
- milestone:: M2

## add-lean-integration

Milestone M3: Expr reflection, marshalling and `deriving Elpi`, quotations, commands and tactics, `lean.*` builtins, the rule DSL and the Lean-facing ELPI libraries.

Depends on [[changes#add-elpi-core]] and [[changes#add-elpi-constraints]]. Capabilities: `lean-reflection`, `lean-integration`, `elpi-runtime-library` (rule DSL), `elpi-libraries` (lean, lean.ltac, lean.derive). Files: `openspec/changes/add-lean-integration/`.

- status:: proposed
- milestone:: M3

## add-elpi-lf

The dependent extension: LF signatures opt-in per file, proof-term recording, export to Lean inductive families, kernel-checked certificates, strategies, mode and totality checking.

Depends on all three earlier changes. Capability: `elpi-lf`. Its design document is the most detailed of the four. Files: `openspec/changes/add-elpi-lf/`.

- status:: proposed
- milestone:: LF
