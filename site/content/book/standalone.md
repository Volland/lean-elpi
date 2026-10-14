---
title: Using it standalone
order: 7
summary: The lean-elpi command, the REPL, include paths, fuel, and ELPI source files.
---
# Using it standalone

The `lean-elpi` executable runs ELPI programs without writing any Lean.

## Command line

```bash
lean-elpi FILE… [-test] [-exec PRED] [-I DIR] [--lean-env M1,M2] [--fuel N] [-- ARGS]
```

| Option | Meaning |
|---|---|
| `-test` | Run the predicate `main` |
| `-exec PRED` | Run `PRED`, passing the arguments after `--` as a list of strings |
| `-I DIR` | Add a directory to the include path for `accumulate` |
| `--lean-env M1,M2` | Import Lean modules so that builtins they register are available |
| `--fuel N` | Limit the number of machine steps, which stops runaway programs |
| `--lf-erase` | Print the erasure of an `#lf` file as plain ELPI |
| `--lf-proof QUERY` | Answer an LF query and print the proof terms |

With several files, they are loaded in order into one program. With no `-test` and no `-exec`, you get the interactive loop.

## The REPL

```text
$ lean-elpi family.elpi
?- ancestor ann X.
Success:
  X = bob
More? (y/N) y
Success:
  X = carl
```

Type a query ending in a dot. Answer `y` for another solution.

## Splitting programs into files

Use `accumulate` to include another file:

```elpi
accumulate helpers.
```

`accumulate helpers.` loads `helpers.elpi`. Names are resolved relative to the including file, then along the `-I` directories. Each file is loaded at most once. LeanElpi bundles a standard library (`std`) and the Lean-facing libraries; they are available without any path.

## Fuel

Every machine step spends one unit of fuel. When it runs out the query stops with a resource error instead of looping forever. Raise it with `--fuel` for heavy searches. The same limit exists in the library API.

## Compatibility with ELPI

The dialect is ELPI 1.18. A shared corpus of programs runs on both the real ELPI and LeanElpi in CI-style conformance runs and the outputs are compared. Known differences are listed in `tests/conformance/divergences.md` in the repository, so you can see exactly where the two engines disagree.
