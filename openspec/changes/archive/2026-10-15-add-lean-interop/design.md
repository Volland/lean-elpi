## Context

The bridge between Lean and ELPI types has to answer three questions: which types cross, who declares them, and how functions cross. The long form is in [[papers/interop#Lean and ELPI types]].

## Decisions

1. **Only plain data crosses.** A type crosses when it is an inductive type or structure with `Type` parameters, no indices and fields that are themselves crossing types. This is exactly the fragment that simple types with prenex polymorphism express, so ELPI unification stays decidable ([[constraints#CIC unification is undecidable]]). Indexed families, `Prop`-valued fields, dependent fields and functions stay on the Lean side, or go through `Expr` reflection or the LF extension.
2. **One declaration, two sides.** Whichever side declares the type, the other side is generated: `deriving Elpi` produces the ELPI `kind`/`type` declarations from a Lean type, and `elpi_data` produces the Lean inductive from ELPI declarations and then runs the same `deriving Elpi`. The ELPI declarations of a type therefore always come from one code path, which is why round trips can be tested rather than assumed.
3. **Recursion through a local instance.** The generated `partial def`s bind a local instance for the type being defined (`let _ : ToElpi (T α) := ⟨T.toElpiImpl⟩`), so a recursive occurrence and a nested one (`List (Rose α)`) are resolved by ordinary instance search.
4. **Functions cross through a class, not through glue.** `ElpiFn F R` peels the arguments of a Lean function type one by one with `FromElpi`; `Extern.total`, `Extern.partial_` and `Extern.many` turn the final result into zero, one or many ELPI solutions. The wrapper is registered as a tier T2 builtin ([[papers/solvers#Tier 2: Lean builtins]]), so it is persistent, importable and backtracking-safe without new machinery.
5. **Failure rather than crash.** A decoding failure of an argument makes the predicate fail, because ELPI's own type checker has already ruled out ill-typed calls at load time.
6. **Name policy.** The ELPI name of a kind is the Lean name with a lower-case first letter; `elpi_data` requires lower-case kinds so the mapping is a bijection. A structure is the single-constructor type whose constructor is `<kind>.mk`.

## Risks and trade-offs

- Type variables are named `A`, `B`, … by position, so the ELPI text does not show the Lean parameter names.
- `elpi_extern` evaluates the wrapper with the interpreter in the defining file; imported modules use the compiled code.
- Higher-order constructor arguments (`(tm -> tm) -> tm`) are rejected by `elpi_data`, because a Lean inductive cannot have the negative occurrence. They remain available as `Expr` or as LF signatures.

## Open questions

- Type-class interoperability (Lean instance resolution as an ELPI `elpi_instance` provider, and the converse) is left for a later change.
