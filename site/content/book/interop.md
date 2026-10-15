---
title: Sharing types between Lean and λProlog
order: 9
summary: Declare a data type, a function or an inductive type on one side and use it on the other, and what Coq-Elpi taught us about doing so.
---
# Sharing types between Lean and λProlog

A λProlog program that cannot talk about your data is a toy. This chapter shows how types, functions and whole inductive declarations move between Lean and ELPI without hand-written glue.

It assumes the previous chapter, [Using it inside Lean](/book/inside-lean/). Every example here is a test in the repository, so the output shown is real.

## The problem

Lean and ELPI describe data differently. Lean has dependent types, ELPI has simple types with type variables. Lean has `inductive Tree (α : Type)`, ELPI has `kind tree type -> type`. In the first release you could pass a `Nat` or a `List Nat` across the boundary, derive the ELPI declarations of a *simple* Lean type, and call `MetaM` from ELPI. Three things were missing:

- a type with a parameter, or a recursive type, could not be derived at all;
- a type you designed in ELPI had to be written a second time in Lean;
- calling an ordinary Lean function from ELPI meant writing untyped glue by hand.

Coq-Elpi, the λProlog layer of the Coq proof assistant, solved similar problems with one idea: *declarations are data, and host functions are typed predicates*. LeanElpi now has the same, adapted to Lean.

## What crosses

A type crosses the boundary when ELPI's simple types can express it. We call that **plain data**: an inductive type or structure whose parameters are `Type`, with no indices, and whose fields are plain data too.

| Lean | ELPI |
|---|---|
| `Nat`, `Int`, `String`, `Bool`, `Float` | `int`, `int`, `string`, `bool`, `float` |
| `List α`, `Option α`, `α × β` | `list A`, `option A`, `pair A B` |
| `Lean.Expr`, `Lean.Name` | `term`, `name` |
| `inductive Tree (α : Type)` | `kind tree type -> type.` |

Indexed families such as `Vec α n` and proofs do not cross as data. Reflect them as `term`, or use the LF layer.

## From Lean to ELPI: deriving

Add `deriving Elpi` to a type and you get the ELPI declarations and the conversion functions. Parameters and recursion work:

```lean
inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (a : α) (r : Tree α)
  deriving Elpi

#elpi_signature Tree
```

The infoview shows what ELPI now knows about the type:

```
kind tree type -> type.
type leaf tree A.
type node tree A -> A -> tree A -> tree A.
```

The Lean parameter `α` became the ELPI type variable `A`. Variables are named by position, `A` then `B`, because ELPI type variables must be capitalised. The instances `[ToElpi α] → ToElpi (Tree α)` and `[FromElpi α] → FromElpi (Tree α)` are generated too, so a `Tree Nat` goes to ELPI and a `Tree Nat` comes back:

```lean
#eval (fromElpi (toElpi (Tree.node .leaf 3 .leaf)) : Except DecodeError (Tree Nat)) |>.isOk
```

Decoding is checked. A `Tree String` decoded at `Tree Nat` is a `DecodeError`, not a crash.

## From ELPI to Lean: `elpi_data`

Sometimes the type belongs to the logic program. Write it there, and Lean gets the inductive for free:

```lean
elpi_data lp%{
  kind shape type.
  type circle int -> shape.
  type square int -> shape.
  type beside shape -> shape -> shape.
}%
```

This defines `inductive Shape` with three constructors and `deriving Elpi`, so the ELPI declarations are the ones you wrote. Now a program can compute with shapes and Lean can read the answers at the right type:

```lean
elpi_program areas
elpi_accumulate areas lp%{
  accumulate lean.
  pred area i:shape, o:int.
  area (circle R) A :- A is 3 * R * R.
  area (square S) A :- A is S * S.
  area (beside X Y) A :- area X A1, area Y A2, A is A1 + A2.

  pred mirror i:shape, o:shape.
  mirror (beside X Y) (beside Y1 X1) :- !, mirror X X1, mirror Y Y1.
  mirror S S.
}%

#eval show MetaM _ from do
  let m ← Elpi.query areas "mirror (beside (circle 1) (square 2)) M"
  return m.head?.bind fun | .ok sol => (sol.get? "M" : Option Shape) | _ => none
```

The result is `some (Shape.beside (Shape.square 2) (Shape.circle 1))`, an ordinary Lean value. A kind with the single constructor `point.mk` becomes a Lean `structure`.

Some ELPI types have no Lean counterpart, and `elpi_data` says so instead of guessing. A constructor such as `type lam (tm -> tm) -> tm` is rejected: a Lean inductive cannot contain that function type. Use `term` for syntax with binders. Nothing is defined if there is any error.

## Lean functions as predicates

`elpi_extern` turns a typed Lean function into an ELPI predicate. The ELPI signature is worked out from the Lean type:

```lean
def twice (n : Nat) : Nat := 2 * n
elpi_extern twice                          -- pred twice i:int, o:int.

def half (n : Nat) : Option Nat :=
  if n % 2 == 0 then some (n / 2) else none
elpi_extern partial half                   -- fails when the result is none

def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => d != 0 && n % d == 0
elpi_extern many divisors as "divisor"     -- one solution per element
```

The three forms match the three kinds of predicate. A total function has one solution, a partial function has at most one, and a multi-valued function has many, in order:

```lean
#elpi myprog lp%{ twice 21 X }%          -- X = 42
#elpi myprog lp%{ half 7 X }%            -- no solution
#elpi myprog lp%{ divisor 12 D }%        -- D = 1, then 2, 3, 4, 6, 12
```

Arguments can be any plain type, including your own derived types. `def trSize (t : Tr Nat) : Nat` becomes a predicate whose first argument has the ELPI type `tr int`. Because the signature is declared, ELPI's type checker rejects `twice "x" X` when the program is loaded.

## Reading and writing inductive types from ELPI

Everything so far moves *values*. Sometimes a program should create a *type*. Two builtins do that:

- `lean.env.indt Name Indt` reads a complete inductive type: its parameters, indices, type and constructors.
- `lean.add_inductive Indt` adds one to the environment, with `casesOn`, `recOn`, `noConfusion` and the other constructions you would get from `inductive`.

Here is a command that copies an inductive type under a new name. It is about as long as the sentence describing it:

```lean
elpi_program cloner
elpi_accumulate cloner lp%{
  accumulate lean.
  pred main i:list argument.
  pred rename-ctor i:string, i:string, i:lean.ctor, o:lean.ctor.
  rename-ctor From To (lean.ctor CN T) (lean.ctor CN1 T1) :-
    lean.name->string CN CS,
    L is size From, N is size CS, M is N - L, Rest is substring CS L M,
    CS1 is To ^ Rest, lean.string->name CS1 CN1, copy T T1.
  main [str From, str To] :-
    lean.string->name From FN, lean.string->name To TN,
    lean.env.indt FN (lean.indt _ NP NI Ty Cs),
    ( pi L\ copy (const FN L) (const TN L) ) => (
      copy Ty Ty1, std.map Cs (rename-ctor From To) Cs1 ),
    lean.add_inductive (lean.indt TN NP NI Ty1 Cs1).
}%
elpi_command clone := cloner
elpi_export clone

clone "Option" "MyOption"

def MyOption.get (d : Nat) : MyOption Nat → Nat
  | .none => d
  | .some x => x

example : (MyOption.some 3).get 0 = 3 := rfl
```

`MyOption` supports pattern matching and `rfl` proofs because `lean.add_inductive` builds the same auxiliary definitions as the `inductive` command. Like `lean.add_decl`, it works only under commands: a tactic that tries it fails with an error and the environment stays unchanged. And the kernel still checks everything, so a wrongly built inductive is rejected whatever your ELPI program believed.

This is the Lean version of Coq-Elpi's `coq.env.indt` and `coq.env.add-indt`, the pair that the whole `derive` family of Coq tools is written with. With them, deriving a map function or a decidable equality for a type can be written as a short λProlog program.

## What we learned from Coq-Elpi

Coq-Elpi has had ten years of use, and four of its lessons were worth copying:

- **Declarations are data.** A program that can read and build inductive declarations can derive things.
- **Host functions are typed predicates.** Declared types and modes let the ELPI checker find mistakes before anything runs.
- **Quotations in both directions.** `{{ … }}` and `lp:` already existed in LeanElpi.
- **One source of truth.** Coq-Elpi keeps its own data types in Elpi and converts by hand. We generate each side from one declaration, so the two cannot drift apart.

One lesson did not transfer. Coq-Elpi shares *the whole term language* of Coq between host and logic program, because for Coq users the terms are the data. Lean programs are full of data that is not an `Expr`, so LeanElpi needs a second path next to reflection, which is plain derived data.

## Limits

- Indexed families, proofs and dependent fields do not cross as plain data.
- `elpi_data` refuses higher-order constructors. Use `term`, or the LF layer.
- Type classes are not bridged yet. Lean instance resolution and ELPI clause resolution are both tabled proof search, so this is the natural next step.
- Variables are named `A`, `B`, … by position; the Lean names of parameters are not kept in the ELPI text.

## Next

The [LF chapter](/book/lf/) covers the dependent side that this chapter deliberately leaves out, and the [design paper](https://github.com/Volland/lean-elpi/blob/main/tg.md/papers/interop.md) has the full reasoning.
