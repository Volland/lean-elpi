---
title: Types and modes
order: 5
summary: Declaring kinds, types and predicates, and what input and output modes mean.
---
# Types and modes

ELPI is typed. Types catch most mistakes before a program runs, and they let the engine pick the right overload and print errors early.

## Kinds and constructors

```elpi
kind nat type.
type z nat.
type s nat -> nat.
```

`kind` declares a new type. `type` declares a constructor or constant with its type. Several constants can share a declaration: `type ann, bob, carl person.`

## Predicates and modes

```elpi
pred plus i:nat, i:nat, o:nat.
plus z N N.
plus (s M) N (s R) :- plus M N R.
```

`pred` declares a predicate, its argument types, and a **mode** for each argument:

- `i:` is an **input**: the argument is matched, never assigned. The caller must supply it.
- `o:` is an **output**: the predicate produces it.

Modes are not just documentation. For an input argument the engine *matches* the clause head against the call instead of unifying, so a call with a still-unknown input does not silently bind it. They also guide indexing, which makes clause selection fast.

With these declarations, `plus (s (s z)) (s z) R` gives `R = s (s (s z))`.

## Polymorphism

Type variables are uppercase. `pred append i:list A, i:list A, o:list A.` works on any element type. Type checking infers and checks the instances at each use.

## Errors you will see

A misuse is reported with a position before anything runs:

- `unknown type 'tm'`: a type was used before its `kind` declaration. Declare types first.
- `application of :: has type (list string) but is used with type string`: an argument has the wrong type.

## Two kinds of "mode"

If you also use the LF layer, note that its `#mode` directive is a different thing. ELPI's `i:`/`o:` changes how the engine runs a predicate. The LF `#mode plus +N +M -P` is a *static* check that inputs are ground, and it never changes execution. The [LF chapter](/book/lf/) covers it.
