# LeanElpi

**λProlog inside Lean 4.** Write tactics, commands and proof search as logic programs, share
types and functions with Lean in both directions, and get proofs the Lean kernel checks.

LeanElpi is a clean-room, native Lean 4 implementation of the [ELPI](https://github.com/LPCIC/elpi)
dialect of λProlog, the language behind Coq-Elpi. It embeds in Lean as a metaprogramming tool (commands, tactics,
`MetaM` builtins), works as a pure library for ordinary Lean programs, ships a
standalone `lean-elpi` binary, and adds an opt-in LF layer with kernel-checked proof
terms.

**Status:** version 0.3: the engine, constraints, Lean integration, the LF layer and the Lean/ELPI type bridge are implemented. Documentation site and book: https://volland.github.io/lean-elpi/ (sources in `site/`, built into `docs/` with `python3 site/build.py`).

## Use it in your project

Add LeanElpi as a Lake dependency (Lean 4.35.0, no Mathlib needed):

```lean
-- lakefile.lean
require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.3.1"
```

or in `lakefile.toml`:

```toml
[[require]]
name = "lean-elpi"
git = "https://github.com/Volland/lean-elpi"
rev = "v0.3.1"
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

## From Python, Node.js and Rust

One native library serves three bindings: load a program once, extend it, query it many times.

```bash
pip install leanelpi        # Python
npm install @lean-elpi/leanelpi   # Node.js
cargo add leanelpi          # Rust (needs the native library, see the guide)
```

```python
from leanelpi import Program
Program("pred n o:int.\nn 1.\nn 2.").solve("n X")   # two solutions: X = 1, X = 2
```

macOS and Linux, no Lean installation needed. Guide: [From Python, Node.js and Rust](https://volland.github.io/lean-elpi/book/bindings/); release steps: [PUBLISHING.md](PUBLISHING.md).

## What it does

- **ELPI engine in Lean**: typed clauses, `pi`/`=>`, higher-order pattern unification, modes, constraints and CHR, a command-line tool, and a lazy library API.
- **Lean integration**: `{{ … }}` quotations, tactics and commands written in λProlog, `lean.*` builtins over `MetaM`, a typed rule DSL.
- **Type bridge** (new in 0.2): `deriving Elpi` for parametric and recursive types, `elpi_data` (ELPI types to Lean inductives), `elpi_extern` (typed Lean functions as ELPI predicates), `lean.env.indt` / `lean.add_inductive` (read and create inductive types from ELPI).
- **Bindings**: Python, Node.js and Rust packages over a C interface, with the Lean runtime inside one shared library.
- **LF layer**: dependently typed signatures, recorded proof terms, export to Lean inductives, kernel-checked certificates.

## Performance and compatibility

Measured against ELPI 1.18 on ELPI's own performance programs (`tests/bench`), release 0.3.1 is about 3 times slower by geometric mean (1.1 to 10.5 times, 50 to 200 MB of memory); release 0.3.0 was 31 times slower. It passes 43 of the 114 upstream ELPI tests that apply and 38 of 40 corpus programs, and 11 of the 21 performance programs are still rejected by the parser, type checker or a missing builtin. Details, the known failures and how to reproduce: the blog posts [compatibility and performance](https://volland.github.io/lean-elpi/blog/compatibility-and-performance/) and [why it was slow](https://volland.github.io/lean-elpi/blog/why-leanelpi-was-slow/).

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
