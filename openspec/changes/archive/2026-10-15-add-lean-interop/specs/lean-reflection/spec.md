## MODIFIED Requirements

### Requirement: Deriving Elpi
`deriving Elpi` on an inductive type or structure SHALL generate `ToElpi` and `FromElpi` instances and the ELPI declarations of the type, which every program can accumulate:
- A `kind` declaration named after the type with its first letter lowercased, taking one `type` argument per type parameter.
- For each constructor of an inductive, a `type` declaration named after the constructor's short name; the type parameters appear as the ELPI type variables `A`, `B`, … in parameter order.
- For a structure, a single constructor named `<kind>.mk`.

Field types SHALL be mapped through their own `ToElpi` instances, recursive and nested occurrences of the type itself (`T α`, `List (T α)`) included, and a field whose type has no instance SHALL be reported as an error at the `deriving` clause. An indexed family, and a type with a parameter that is not a `Type`, SHALL be rejected with an error. A generated name that clashes with an existing ELPI constant SHALL also be reported as an error, not silently shadowed. The instances of a parametric type SHALL require instances for its parameters.

#### Scenario: Inductive emits kind and type declarations
- **WHEN** `inductive Color | red | green deriving Elpi` is elaborated
- **THEN** the ELPI declarations `kind color type.`, `type red color.` and `type green color.` are registered
- **AND** `ToElpi.toElpi Color.red` is the ELPI constant `red`

#### Scenario: Structure emits a constructor declaration
- **WHEN** `structure Point where x : Nat; y : Nat deriving Elpi` is elaborated
- **THEN** the ELPI declarations `kind point type.` and `type point.mk int -> int -> point.` are registered
- **AND** `FromElpi.fromElpi (point.mk 1 2)` returns `.ok ⟨1, 2⟩`
