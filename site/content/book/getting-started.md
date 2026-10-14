---
title: Getting started
summary: Install LeanElpi and run a first program, standalone and inside Lean.
order: 2
---
# Getting started

LeanElpi ships as a Lake package for Lean 4 and as a command-line program. This chapter builds both and runs the same small program three ways.

## Build it

You need [Lean 4 via elan](https://lean-lang.org/install/). The project pins its toolchain in `lean-toolchain`.

```bash
git clone https://github.com/Volland/lean-elpi
cd lean-elpi
lake build
```

The build produces the library and the `lean-elpi` executable at `.lake/build/bin/lean-elpi`.

## Use it from your own Lake project

Add it as a dependency in your `lakefile.lean`:

```lean
require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.1.0"
```

Then `import Elpi` in any Lean file.

## A first program

Save this as `family.elpi`:

```elpi
kind person type.
type ann, bob, carl person.

pred parent o:person, o:person.
parent ann bob.
parent bob carl.

pred ancestor o:person, o:person.
ancestor X Y :- parent X Y.
ancestor X Z :- parent X Y, ancestor Y Z.

main :- ancestor ann carl, print "ann is an ancestor of carl".
```

### 1. As a standalone program

```bash
.lake/build/bin/lean-elpi family.elpi -test
```

`-test` runs the predicate `main`. You can also run any predicate with `-exec`, or start the interactive loop by giving no query:

```bash
printf 'ancestor ann X.\n' | .lake/build/bin/lean-elpi family.elpi
```

The REPL prints each answer and asks whether you want more.

### 2. Inside Lean

```lean
import Elpi
open Elpi.Cmd

elpi_program family
elpi_accumulate family lp%{
  kind person type.
  type ann, bob, carl person.
  pred parent o:person, o:person.
  parent ann bob.
  parent bob carl.
  pred ancestor o:person, o:person.
  ancestor X Y :- parent X Y.
  ancestor X Z :- parent X Y, ancestor Y Z.
}%

#elpi family lp%{ ancestor ann X }%
```

Lean prints `X = bob`. The block `lp%{ … }%` holds raw ELPI source; errors inside it are reported at the right line of your Lean file. `#elpi` shows one answer by default; set `elpi.solutions` to see more.

### 3. As a library

```lean
import Elpi
open Elpi

#eval show IO Unit from do
  match Program.load "p 1. p 2." with
  | .ok prog =>
    for r in (solve prog "p X").toList do
      match r with
      | .ok s => IO.println s
      | .error e => IO.println s!"{e}"
  | .error e => IO.println s!"{e}"
```

`solve` returns a lazy stream of answers, so asking for the first one costs only the first one. This prints `X = 1` and `X = 2`.

## What next

The next chapters teach the language from the ground up. If you already know Prolog, skim [Terms, clauses and search](/book/first-programs/) and go straight to [Higher-order programming](/book/higher-order/).
