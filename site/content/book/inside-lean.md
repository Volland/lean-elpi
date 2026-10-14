---
title: Using it inside Lean
order: 8
summary: Programs, queries, quotations, tactics and commands written in λProlog.
---
# Using it inside Lean

With `import Elpi`, a Lean file can hold ELPI programs, run them, and let them read and build Lean terms.

## Programs and queries

```lean
import Elpi
open Elpi.Cmd

elpi_program family
elpi_accumulate family lp%{
  kind person type.
  type ann, bob person.
  pred parent o:person, o:person.
  parent ann bob.
}%

#elpi family lp%{ parent ann X }%
```

- `elpi_program name` declares a program. It also defines a Lean constant `name`.
- `elpi_accumulate name lp%{ … }%` adds source to it. You can also accumulate a file: `elpi_accumulate name file "rules.elpi"`.
- `#elpi name lp%{ query }%` runs a query and reports the first solution.
- `elpi_db name` declares a database that several programs can share.

Programs are compiled when declared, so a type error in the ELPI source is a Lean error at that position.

## Lean terms inside λProlog

Lean expressions are reflected as ELPI terms using higher-order syntax: `lam`, `app`, `const`, `sort`, `lit` and so on, where `lam` holds a function in its body so that binders are handled by the logic. You rarely write these by hand. Use the quotation `{{ … }}`:

```lean
#elpi family lp%{ X = {{ 1 + 2 }}, print X }%
```

Inside `{{ … }}` you write ordinary Lean syntax. It is elaborated and turned into a term. Inside a quotation, `lp:{{ X }}` splices an ELPI variable back in, so you can build and take apart Lean terms with patterns.

## Builtins that talk to Lean

With `accumulate lean.` a program gets predicates such as `lean.infer` (type of a term), `lean.add_decl` (add a declaration), and name and universe helpers. They run in `MetaM`, so they see your environment.

## Tactics

A tactic is a predicate `solve` that takes the goal and returns new goals. The combinator library `lean.ltac` provides `then`, `orelse`, `intro`, `exact`, `apply` and `assumption`:

```lean
elpi_program intro_assume_prog
elpi_accumulate intro_assume_prog lp%{
  accumulate lean.ltac.
  pred solve i:goal, i:list argument, o:list goal.
  solve G _ Gs :- lean.ltac.then (lean.ltac.intro "h") lean.ltac.assumption G Gs.
}%
elpi_tactic intro_assume := intro_assume_prog

theorem t (p : Prop) : p → p := by elpi intro_assume
```

The result is checked by Lean as usual, so a wrong tactic cannot prove a false theorem.

## Commands

A command is a predicate `main` that takes a list of arguments:

```lean
elpi_program cmdprog
elpi_accumulate cmdprog lp%{
  accumulate lean.
  pred main i:list argument.
  main [trm (const _ _), int I, str S] :-
    lean.string->name S N,
    lean.add_decl (lean.def N {{Nat}} (lit (nat I))).
}%
elpi_command mycmd := cmdprog
elpi_export mycmd

mycmd Nat.succ 3 "answer"
example : answer = 3 := rfl
```

`elpi_export` makes the command available by name, and the arguments are parsed into ELPI data (`trm`, `int`, `str`).

## Deriving

`deriving Elpi` generates the conversions that move your Lean data types in and out of ELPI, including the type declarations. This is how the library call `solveAs` can return a Lean structure instead of a raw term.

## As a plain library

When you do not need `MetaM`, the engine is a pure Lean library: `Program.load` compiles a source string, and `solve` yields a lazy stream of solutions. The rule DSL (`elpi_rules`) lets you write predicates as Lean declarations and get typed Lean queries back.
