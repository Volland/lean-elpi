# LeanElpi

A clean-room, native Lean 4 implementation of the [ELPI](https://github.com/LPCIC/elpi)
dialect of λProlog. It embeds in Lean as a metaprogramming tool (commands, tactics,
`MetaM` builtins), works as a pure library for ordinary Lean programs, ships a
standalone `lean-elpi` binary, and adds an opt-in LF layer with kernel-checked proof
terms.

**Status:** version 0.1: the engine, constraints, Lean integration and the LF layer are implemented. Documentation site and book: https://volland.github.io/lean-elpi/ (sources in `site/`, built into `docs/` with `python3 site/build.py`).

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
