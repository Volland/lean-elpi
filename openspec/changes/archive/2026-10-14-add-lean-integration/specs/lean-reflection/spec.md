## Purpose

Reflection of Lean data into ELPI and back. It covers the higher-order abstract syntax (HOAS) `term` type that mirrors every `Lean.Expr` form, a lossless round trip with universe levels kept as opaque handles, the `ToElpi`/`FromElpi` marshalling classes, `deriving Elpi`, and Lean quotations inside ELPI source.

## ADDED Requirements

### Requirement: HOAS term encoding
The system SHALL provide an ELPI type `term` whose constructors cover every `Lean.Expr` form except `bvar`:
- `const Name Levels`
- `app Head Args`, the maximal application spine, with a `Head` that is never an `app`
- `fun N Ty (x\ B)`
- `forall N Ty (x\ B)`, for a Lean `forallE`
- `let N Ty V (x\ B)`
- `sort L`
- `lit L`
- `mvar M`
- `fvar F`
- `proj S I T`
- `mdata D T`

Bound variables SHALL be represented by ELPI λ-abstraction, so reflected terms never expose de Bruijn indices, and substituting into a body is ELPI β-reduction. Literals SHALL be values of the ELPI type `literal`: `nat N`, where `N` is an arbitrary-precision natural written as an integer literal, or `str S`. Constant names SHALL be values of an opaque ctype `name`, written and printed as string literals in their escaped Lean form. The binder argument `N` SHALL be an opaque ctype `binder` that carries the user name, the binder info and, for `let`, the non-dependency flag. Reflecting an `Expr` with loose bound variables SHALL fail with an error, not produce an ill-scoped term.

#### Scenario: Lean binder becomes an ELPI lambda
- **WHEN** `fun (x : Nat) => x` is reflected
- **THEN** the result is `fun N (const "Nat" []) (x\ x)`, where `N` is a binder handle displaying `x`
- **AND** the ELPI goal `T = fun _ _ F, R = F (lit (nat 3))` binds `R` to `lit (nat 3)` by β-reduction

#### Scenario: Constructors cover every Expr form
- **WHEN** a test reflects one sample `Expr` for each of `const`, `app`, `lam`, `forallE`, `letE`, `sort`, `lit` (natural and string), `mvar`, `fvar`, `proj` and `mdata`
- **THEN** each result has the head constructor listed for that form, and no result contains a `bvar` encoding
- **AND** reflecting `Expr.bvar 0` on its own fails with a "loose bound variable" error

### Requirement: Lossless Expr round trip
For every closed `Expr` `e` that is well formed in the current environment, reifying the reflection of `e` SHALL return an `e'` with `e.equal e'`. That means binder names, binder info, `let` non-dependency flags, universe levels, metadata, projections, literal values (including naturals larger than ELPI `int`) and metavariable and free-variable identities are all preserved. Reification of a `term` that ELPI built SHALL produce a well-formed `Expr`, with ELPI unification variables turned into fresh Lean metavariables when the caller allows that, and an error when it does not.

#### Scenario: Round trip preserves universe levels
- **WHEN** `@List.map.{u, v}` and `Sort (max u v + 1)` are reflected and then reified
- **THEN** each result is `Expr.equal` to its input, with the level parameters `u` and `v` and the `max … + 1` structure intact

#### Scenario: Round trip preserves metadata and projections
- **WHEN** `Expr.mdata {pp.analysis.skip := true} (Expr.proj ``Prod 0 p)` is reflected and then reified
- **THEN** the result is `Expr.equal` to the input, keeping the metadata map, the structure name `Prod` and the index `0`

### Requirement: Opaque universe levels
Universe levels SHALL be reflected as values of an opaque ctype `level`. Structurally equal levels SHALL get identical handles (they are hash-consed), and ELPI unification SHALL compare level handles by identity only: a level handle never unifies with a different handle, even when the two levels are equal up to Lean's level normalisation. ELPI code that needs level equivalence SHALL ask Lean, for example through `lean.defeq` on the corresponding sorts.

#### Scenario: Levels compare by handle identity
- **WHEN** `Sort u` is reflected twice and the ELPI goal `sort L1 = sort L2` is run on the two results
- **THEN** the goal succeeds
- **AND** the same goal on the reflections of `Sort (max u v)` and `Sort (max v u)` fails, while `lean.defeq` on those two sorts succeeds

### Requirement: Typed marshalling classes
The system SHALL provide `class ToElpi (α : Type)` and `class FromElpi (α : Type)`, encoding Lean values as ELPI terms and decoding them back. They SHALL ship with instances for `Nat` and `Int` (as ELPI `int`), `String`, `Bool`, `Float`, `Name`, `Expr` (as `term`), `Level` (as `level`), `List`, `Option`, `Prod` and `Array`. For every instance pair, `fromElpi (toElpi a) = .ok a` SHALL hold. Decoding SHALL return a structured error naming the expected ELPI type and the term it got, and SHALL never panic. A `Nat` or `Int` outside the ELPI `int` range SHALL fail to encode with an overflow error instead of wrapping.

#### Scenario: Nat round-trips through ToElpi and FromElpi
- **WHEN** `FromElpi.fromElpi (ToElpi.toElpi (42 : Nat))` and `FromElpi.fromElpi (ToElpi.toElpi [(1, "a"), (2, "b")])` are evaluated
- **THEN** they return `.ok 42` and `.ok [(1, "a"), (2, "b")]`

#### Scenario: Decoding a wrong shape fails
- **WHEN** the ELPI string `"x"` is decoded with `FromElpi.fromElpi (α := Nat)`
- **THEN** the result is `.error` with a message naming the expected type `int` and the term `"x"`

### Requirement: Deriving Elpi
`deriving Elpi` on an inductive type or structure SHALL generate `ToElpi` and `FromElpi` instances and the ELPI declarations of the type, which every program can accumulate:
- A `kind` declaration named after the type with its first letter lowercased.
- For each constructor of an inductive, a `type` declaration named after the constructor's short name.
- For a structure, a single constructor named `<kind>.mk`.

Field types SHALL be mapped through their own `ToElpi` instances, and a field whose type has no instance SHALL be reported as an error at the `deriving` clause. A generated name that clashes with an existing ELPI constant SHALL also be reported as an error, not silently shadowed.

#### Scenario: Inductive emits kind and type declarations
- **WHEN** `inductive Color | red | green deriving Elpi` is elaborated
- **THEN** the ELPI declarations `kind color type.`, `type red color.` and `type green color.` are registered
- **AND** `ToElpi.toElpi Color.red` is the ELPI constant `red`

#### Scenario: Structure emits a constructor declaration
- **WHEN** `structure Point where x : Nat; y : Nat deriving Elpi` is elaborated
- **THEN** the ELPI declarations `kind point type.` and `type point.mk int -> int -> point.` are registered
- **AND** `FromElpi.fromElpi (point.mk 1 2)` returns `.ok ⟨1, 2⟩`

### Requirement: Quotations
ELPI source accumulated from Lean SHALL accept Lean term quotations `{{ t }}`. Each one is elaborated in the Lean environment and namespace of the accumulation point and stands for the reflected `term`. Holes `_` in a quotation SHALL become fresh ELPI unification variables. An antiquotation `lp:{{X}}` (the Coq-Elpi convention) inside a quotation SHALL splice the ELPI term `X` into that position: the position is elaborated as a hole of the expected type, and that hole is then replaced by `X`. Elaboration errors inside a quotation SHALL be reported at their Lean source position.

#### Scenario: Quotation elaborates to a term
- **WHEN** the inline source `lp%{ p T :- T = {{ fun x : Nat => x + 1 }}. }%` is accumulated and the query `p T` is run
- **THEN** `T` is bound to a `fun` term whose reification is `Expr.equal` to the elaboration of `fun x : Nat => x + 1`

#### Scenario: Antiquotation splices an ELPI variable
- **WHEN** the query `X = {{ (2 : Nat) }}, T = {{ lp:{{X}} + 1 }}` is run
- **THEN** `T` reifies to the elaboration of `(2 : Nat) + 1`, with the reflected `2` in the antiquoted position
