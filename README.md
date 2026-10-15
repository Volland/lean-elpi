# LeanElpi

**λProlog inside Lean 4.** Write tactics, commands and proof search as logic programs, share
types and functions with Lean in both directions, and get proofs the Lean kernel checks.

LeanElpi is a clean-room, native Lean 4 implementation of the [ELPI](https://github.com/LPCIC/elpi)
dialect of λProlog, the language behind Coq-Elpi. It embeds in Lean as a metaprogramming tool (commands, tactics,
`MetaM` builtins), works as a pure library for ordinary Lean programs, ships a
standalone `lean-elpi` binary, and adds an opt-in LF layer with kernel-checked proof
terms.

**Status:** version 0.2: the engine, constraints, Lean integration, the LF layer and the Lean/ELPI type bridge are implemented. Documentation site and book: https://volland.github.io/lean-elpi/ (sources in `site/`, built into `docs/` with `python3 site/build.py`).

## Use it in your project

Add LeanElpi as a Lake dependency (Lean 4.35.0, no Mathlib needed):

```lean
-- lakefile.lean
require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.2.0"
```

or in `lakefile.toml`:

```toml
[[require]]
name = "lean-elpi"
git = "https://github.com/Volland/lean-elpi"
rev = "v0.2.0"
```

Then `import Elpi`:

```lean
import Elpi
open Elpi.Cmd

-- a Lean type, shared with ELPI
inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (a : α) (r : Tree α)
  deriving Elpi

-- a Lean function, callable from ELPI
def twice (n : Nat) : Nat := 2 * n
elpi_extern twice

elpi_program demo
#elpi demo lp%{ twice 21 X }%     -- X = 42
```

## What it does

- **ELPI engine in Lean**: typed clauses, `pi`/`=>`, higher-order pattern unification, modes, constraints and CHR, a command-line tool, and a lazy library API.
- **Lean integration**: `{{ … }}` quotations, tactics and commands written in λProlog, `lean.*` builtins over `MetaM`, a typed rule DSL.
- **Type bridge** (new in 0.2): `deriving Elpi` for parametric and recursive types, `elpi_data` (ELPI types to Lean inductives), `elpi_extern` (typed Lean functions as ELPI predicates), `lean.env.indt` / `lean.add_inductive` (read and create inductive types from ELPI).
- **LF layer**: dependently typed signatures, recorded proof terms, export to Lean inductives, kernel-checked certificates.

See [CHANGELOG.md](CHANGELOG.md) for releases and [CONTRIBUTING.md](CONTRIBUTING.md) to help.

## Where to read

| You want | Read |
|---|---|
| The big picture | `tg.md/overview.md`, then `tg.md/papers/system.md` |
| Why things are the way they are | `tg.md/decisions.md`, `tg.md/alternatives.md` |
| Module layout and UML | `tg.md/architecture/` |
| Exact requirements | `openspec/changes/*/specs/` |
| The plan per milestone | `openspec/changes/<change>/{proposal,design,tasks}.md` |

The docs form a typed knowledge graph read with the `tg` CLI:

```bash
tg search "pattern unification"
tg section "decisions#Persistent store"
tg trace --gaps          # what is not implemented or verified yet
tg check && tg validate  # links, structure, typed edges
```

## Build

```bash
lake build                        # library + lean-elpi executable (Lean 4.35.0)
tests/conformance/run.sh record   # store ELPI 1.18 oracle answers (needs opam elpi)
tests/conformance/run.sh          # compare lean-elpi against the oracle
```

## License

Apache-2.0, clean-room: no upstream ELPI (LGPL-2.1) code is ported or vendored.
