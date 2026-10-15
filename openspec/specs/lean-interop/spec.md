# lean-interop Specification

## Purpose
TBD - created by archiving change add-lean-interop. Update Purpose after archive.

## Requirements

### Requirement: Parametric and recursive deriving
`deriving Elpi` SHALL accept type parameters and recursive types. For `inductive Tree (α : Type)` it SHALL register `kind tree type -> type.` and constructor declarations in which `α` is the ELPI type variable `A`, and a recursive occurrence is `tree A`. Occurrences nested in `List`, `Option`, `Array` and pair types and in other derived types SHALL be supported. The generated instances SHALL be `[ToElpi α] → ToElpi (Tree α)` and `[FromElpi α] → FromElpi (Tree α)`. Decoding a payload of the wrong type SHALL return a `DecodeError`. A type with indices SHALL be rejected with an error that names the LF extension.

#### Scenario: Recursive type derives
- **WHEN** `inductive Typ | base | arr (a b : Typ) deriving Elpi` is elaborated
- **THEN** the declaration `type arr typ -> typ -> typ.` is registered
- **AND** decoding the encoding of `Typ.arr .base (.arr .base .base)` returns the same value

#### Scenario: Parameters become type variables
- **WHEN** `Tree α`, `Box α β` (with a field `List (Option β)`) and `Rose α` (with a field `List (Rose α)`) derive `Elpi`
- **THEN** the declarations `kind tree type -> type.`, `type node tree A -> A -> tree A -> tree A.`, `type box.mk A -> list (option B) -> box A B.` and `type mk A -> list (rose A) -> rose A.` are registered

#### Scenario: Instantiated instance round-trips
- **WHEN** a `Tree Nat` and a `Rose String` are encoded and decoded
- **THEN** the decoded values equal the originals
- **AND** decoding `Tree.node .leaf "x" .leaf` at `Tree Nat` returns a decoding error

#### Scenario: Indexed family is rejected
- **WHEN** `inductive Vec (α : Type) : Nat → Type … deriving Elpi` is elaborated
- **THEN** elaboration fails with the error "Vec is an indexed family, which plain ELPI types cannot express (use the LF extension)"

### Requirement: Signature inspection
`#elpi_signature T` SHALL log the ELPI `kind` and `type` declarations that `deriving Elpi` registered for the Lean type `T`, and SHALL report an error for a type without such declarations.

#### Scenario: Signature is shown
- **WHEN** `#elpi_signature Tree` is elaborated after `Tree` derived `Elpi`
- **THEN** the info message lists `kind tree type -> type.`, `type leaf tree A.` and `type node tree A -> A -> tree A -> tree A.`

### Requirement: ELPI data types
`elpi_data lp%{ … }%` SHALL read plain ELPI `kind` and `type` declarations and define, for each kind, a Lean inductive type (or a structure when the kind has the single constructor `<kind>.mk`) with `deriving Elpi`. The Lean name of a kind SHALL be its name with the first letter capitalised, so kinds SHALL start with a lower-case letter. A kind of arity `n` SHALL give a type with `n` parameters named after the type variables of its constructors. The ELPI types `int`, `string`, `bool`, `float`, `term`, `name`, `level`, `list`, `option` and `pair` SHALL map to `Int`, `String`, `Bool`, `Float`, `Lean.Expr`, `Lean.Name`, `Lean.Level`, `List`, `Option` and `×`. A constructor argument of function type, an unknown ELPI type, a kind without constructors and inconsistent type variables SHALL each be an error naming the constructor and the reason, and nothing SHALL be defined when any error occurs. The ELPI declarations registered for the generated types SHALL be the declared ones.

#### Scenario: Data becomes an inductive
- **WHEN** the block declares `shape` with `circle int -> shape`, `square int -> shape` and `beside shape -> shape -> shape`, and `tree A` with `leaf` and `node`
- **THEN** the Lean types `Shape` and `Tree` exist, `Shape.beside (.circle 1) (.square 2)` round-trips through `ToElpi` and `FromElpi`, and so does a `Tree Int`

#### Scenario: Declarations are preserved
- **WHEN** the block above is elaborated
- **THEN** the registered declarations include `kind shape type.`, `type beside shape -> shape -> shape.` and `type node tree A -> A -> tree A -> tree A.`

#### Scenario: Program and Lean agree on the type
- **WHEN** a program that accumulates only `pred area i:shape, o:int` clauses and `pred mirror i:shape, o:shape` clauses over these declarations is queried with `Elpi.query`
- **THEN** `area (beside (circle 1) (square 2)) A` binds `A` to `7`
- **AND** the binding of `M` in `mirror (beside (circle 1) (square 2)) M` decodes at the Lean type `Shape` to `Shape.beside (.square 2) (.circle 1)`

#### Scenario: Higher-order data is rejected
- **WHEN** the block declares `type lam (tm -> tm) -> tm.`
- **THEN** elaboration fails with the error that the argument is higher-order and that plain data only is supported, and no type is defined

#### Scenario: Unknown ELPI type is rejected
- **WHEN** the block declares `type rule.mk prop -> rule.`
- **THEN** elaboration fails with the error that the ELPI type `prop` has no Lean counterpart

### Requirement: Typed Lean externs
`elpi_extern f` SHALL expose the Lean function `f` as the ELPI predicate named after `f` with a lower-case first letter, or after the string given by `as "name"`. Its signature SHALL be computed from the type of `f`: every argument is an input `i:` of the ELPI type of the Lean argument type and the result is the output `o:`. Argument types and the result type SHALL be types with ELPI counterparts (base types, lists, options, pairs and derived types, parameters instantiated). Arguments SHALL be decoded with `FromElpi` and the result encoded with `ToElpi`; an argument that fails to decode SHALL make the predicate fail. The form `elpi_extern partial f` requires the result type `Option β` and gives one solution for `some` and failure for `none`. The form `elpi_extern many f` requires `List β` and gives one solution per element, in order. The registration SHALL persist in the environment, so it is visible in importing modules, and a name already registered SHALL be an error. A function with a dependent, implicit or function-typed argument, or a universe-polymorphic function, SHALL be rejected with an error.

#### Scenario: Total function
- **WHEN** `def twice (n : Nat) : Nat := 2 * n` and `elpi_extern twice` are elaborated
- **THEN** the query `twice 21 X` in a program binds `X` to `42`, also when called from a clause body

#### Scenario: Partial function
- **WHEN** `def half (n : Nat) : Option Nat` returns `some (n / 2)` for even `n` and `none` otherwise, and `elpi_extern partial half` is elaborated
- **THEN** `half 10 X` binds `X` to `5` and `half 7 X` has no solution

#### Scenario: Multi-valued function
- **WHEN** `def divisors (n : Nat) : List Nat` lists the divisors of `n` and `elpi_extern many divisors as "divisor"` is elaborated
- **THEN** the query `divisor 12 D` has the solutions `D = 1, 2, 3, 4, 6, 12` in this order

#### Scenario: Arguments of derived types
- **WHEN** an extern takes `List Nat` and `String` arguments, and another takes a derived `Tr Nat`
- **THEN** `glue [1, 2] [3] "-" S` binds `S` to `"1-2-3"` and `tr-size (node (node leaf 1 leaf) 2 leaf) N` binds `N` to `2`

#### Scenario: Signature is checked by ELPI
- **WHEN** a program calls `twice "x" X`
- **THEN** the ELPI type checker reports an error and the call is not run

#### Scenario: Unsupported type is rejected
- **WHEN** `elpi_extern bad` is elaborated for `bad : (Nat → Nat) → Nat`
- **THEN** elaboration fails with the error that `Nat -> Nat` has no `ToElpi` instance

### Requirement: Inductive types from ELPI
The system SHALL provide the builtin `lean.env.indt Name Indt`, which reads an inductive type of the Lean environment completely, and the builtin `lean.add_inductive Indt`, which adds one. Both use `lean.indt Name NParams NIndices Type Ctors` with `lean.ctor Name Type` constructors, where all types are reflected terms and a constructor type mentions the inductive as a constant applied to its parameters. `lean.add_inductive` SHALL add the inductive declaration, compile it and build the auxiliary constructions (`casesOn`, `recOn`, `noConfusion`, `below`, `brecOn`), so the new type can be matched on and used for structural recursion exactly like a type declared with `inductive`. It SHALL be available only under commands, with the phase-restriction error of the other environment-changing builtins. A kernel rejection SHALL make the builtin fail with the kernel message in `lean.last-error`.

#### Scenario: Copy of an inductive type
- **WHEN** an ELPI command reads `Option` with `lean.env.indt`, renames the type and its constructors to `MyOption`, `MyOption.none` and `MyOption.some`, and passes the result to `lean.add_inductive`
- **THEN** `MyOption.some 3 : MyOption Nat` elaborates, `MyOption.casesOn` exists, and a function defined by pattern matching on `MyOption` computes by `rfl`

#### Scenario: Phase restriction
- **WHEN** a tactic's `solve` calls `lean.add_inductive`
- **THEN** the tactic fails with the error "lean.add_inductive is only available in commands (current phase: tactic)"
