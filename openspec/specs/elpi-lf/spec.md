# elpi-lf Specification

## Purpose
Provide an opt-in LF (λΠ, Edinburgh Logical Framework) layer on the ELPI engine. An LF signature is checked with dependent types, and LF queries are solved by the same higher-order pattern unifier and machine. Every answer carries a proof term, which is exported to a Lean inductive family and checked by the Lean kernel as a certificate.

The LF surface syntax used throughout this spec:

- Declarations are written `c : A.`; kinds are built from `type`.
- Π is written `pi x:A\ B`.
- `A -> B` is the non-dependent arrow, and `B <- A` means `A -> B`. `<-` is left-associative, and its premises are tried top to bottom.
- Object λ is ELPI's `x\ M`.
- Free uppercase variables in a declaration are implicitly Π-bound, ordered by first occurrence.
- Directives start with `#`.

The running example is the simply typed λ-calculus signature `stlc`:

```
#lf
tp   : type.
arr  : tp -> tp -> tp.
base : tp.
tm   : type.
lam  : tp -> (tm -> tm) -> tm.
app  : tm -> tm -> tm.
of   : tm -> tp -> type.
of_lam : of (lam T1 E) (arr T1 T2)
          <- (pi x:tm\ of x T1 -> of (E x) T2).
of_app : of (app E1 E2) T2
          <- of E1 (arr T1 T2)
          <- of E2 T1.
```

## Requirements

### Requirement: LF opt-in per file

The system SHALL read a source file as an LF signature if and only if its first non-comment line is the header `#lf`. The Lean command `lf_signature <name> <file>` SHALL be equivalent to accumulating a file that carries that header. A file without the header SHALL be parsed, type-checked and executed exactly as in `elpi-core-engine`: no LF checking, no proof recording, and the fixed depth-first order, with the ELPI 1.18 oracle's answers as the reference. LF declarations, LF directives and the `pi x:A\ B` syntax SHALL be rejected with a parse error outside an `#lf` file. An `#lf` file SHALL contain only LF declarations and `#` directives. Plain clauses that use LF predicates SHALL live in plain files that accumulate the LF file.

#### Scenario: lf header enables dependent checking
- **WHEN** the file `stlc.elpi` starts with `#lf` and contains the `stlc` signature plus `bad : of (app base base) base.`
- **THEN** loading fails with an LF type error for `bad`, reported at the position of the first `base` argument of `app` and stating that `tm` was expected and `tp` found
- **AND** the same file without `bad` loads, and `#lf_query stlc (of (lam base x\ x) T)` answers `T = arr base base`

#### Scenario: Plain file is unaffected
- **WHEN** a plain file with no `#lf` header declares `kind tm type.`, `type app tm -> tm -> tm.` and clauses for a predicate `size`, and is run by `lean-elpi` and by the ELPI 1.18 oracle
- **THEN** both report the same answers in the same order
- **AND** no LF checking runs, no proof term is recorded, and declaring a strategy with `#strategy iddfs` in that file is a parse error

### Requirement: Dependent signatures

In an `#lf` file, the system SHALL check every declaration against the canonical λΠ typing rules:

- a family constant `a : K` SHALL have a well-formed kind `K`;
- an object constant `c : A` SHALL have a type `A` that checks against `type`;
- every object occurring in an index SHALL check against the type its family expects, with equality on canonical forms up to α-conversion and with no other conversion.

The system SHALL reconstruct the types of implicitly bound uppercase variables. A variable whose type cannot be determined uniquely SHALL be reported as an error that names the variable. Every LF type error SHALL report the declaration name, the source position, and the expected and found types. A signature that has been loaded SHALL be well typed in every declaration.

#### Scenario: Ill-typed LF object is rejected
- **WHEN** an `#lf` file declares the `stlc` signature followed by `bad2 : of (lam base base) base.`
- **THEN** loading fails with an error naming `bad2`, its line and column, and stating that the second argument of `lam` was expected to have type `tm -> tm` but has type `tp`
- **AND** no constant from the file is added to the program

#### Scenario: Type family is indexed by objects
- **WHEN** an `#lf` file declares `nat : type. z : nat. s : nat -> nat. vec : nat -> type. vnil : vec z. vcons : nat -> vec N -> vec (s N).`
- **THEN** the signature loads, and querying the reconstructed type of `vcons` reports `pi N:nat\ nat -> vec N -> vec (s N)`
- **AND** a declaration `wrong : vec (s z) <- vec z.` loads, while `wrong2 : vec base.` in the same file fails, because the index `base` is not a `nat`

### Requirement: Pattern unification for LF

The system SHALL unify LF objects with the higher-order pattern unifier of `elpi-core-engine`, applied to their erased forms. Implicit arguments SHALL be kept explicit in the erased forms, so that type indices are unified as ordinary arguments. Before unification, objects SHALL be brought to canonical, η-long form as their LF types direct. A unification problem in the pattern fragment SHALL be solved by its most general unifier. A problem outside the pattern fragment SHALL be suspended as a delayed goal and never solved by guessing. An LF answer that still has suspended unification problems when search ends SHALL be reported together with those residual problems and SHALL NOT be certified.

#### Scenario: LF unification stays in the pattern fragment
- **WHEN** the query `of (lam base (y\ app y y)) T` runs against `stlc`
- **THEN** unifying with the head of `of_lam` binds `E` to `y\ app y y` through the pattern problem `E x = app x x`, with `x` an eigenvariable, and the query fails finitely with no residual constraints
- **AND** with a signature that extends `stlc` by `c : tm. p : tm -> type. p_c : p c. q : (tm -> tm) -> type. q_c : q F <- p (F (app c c)).`, the query `q G` suspends the non-pattern problem `G (app c c) = c`, and its answer is reported with that residual constraint and refused for certification

### Requirement: Proof term recording

The system SHALL record a proof term for every successful LF query. The proof term SHALL be an LF object whose type is the query instantiated by the answer substitution, written in fully explicit form with implicit arguments included. A resolution step that uses constant `c` SHALL add `c` applied to its implicit-argument instances and to the proof terms of its premises. A universal goal `pi x:A\ G` SHALL add a λ that binds `x`. A hypothetical goal `A -> G` SHALL add a λ that binds a fresh hypothesis variable, and a use of that hypothesis SHALL add the variable as the head. Backtracking SHALL discard every part of a proof term built on the abandoned branch, so each answer's proof term reflects only the derivation of that answer.

#### Scenario: Successful query yields a derivation term
- **WHEN** `#lf_query stlc (of (lam base x\ x) T)` runs
- **THEN** it reports `T = arr base base` and the proof term `of_lam base (x\ x) base (x\ u\ u)`
- **AND** the LF checker accepts that proof term at type `of (lam base x\ x) (arr base base)`

### Requirement: Lean inductive export

The command `lf_export <sig>` SHALL generate Lean declarations for an LF signature in a namespace derived from the signature name, and the Lean kernel SHALL accept them.

- Each **syntax family** SHALL become an inductive type in `Type`. A syntax family is one whose objects appear as indices of other families. If its objects contain binders (arguments of function type such as `tm -> tm`), its inductive SHALL be indexed by a scope: a well-scoped de Bruijn encoding with a generated variable type.
- Each **judgment family** SHALL become an inductive family in `Prop`. A judgment family is one whose constants serve as derivation rules. Its inductive SHALL be indexed by an explicit context of hypotheses and by the exported indices. A hypothetical premise SHALL become a premise over an extended context, and an assumption SHALL become a lookup constructor.
- Each LF object constant SHALL become exactly one constructor, with the same name and with its arguments in the order of its LF type.

A signature outside the exportable fragment SHALL be rejected by `lf_export` with an error naming the offending declaration, and SHALL remain usable for search. A constructor that takes a judgment as a function argument is outside the fragment, and so is a hypothesis that is not atomic.

#### Scenario: Type family compiles to an inductive family
- **WHEN** `lf_export stlc` runs
- **THEN** it adds the following to namespace `Stlc`:
  - `Tp : Type` with constructors `arr` and `base`;
  - `Var : Nat → Type`;
  - `Tm : Nat → Type` with constructors `var : Var n → Tm n`, `lam : Tp → Tm (Nat.succ n) → Tm n` and `app : Tm n → Tm n → Tm n`;
  - a context type `Ctx : Nat → Type`;
  - `Of : Ctx n → Tm n → Tp → Prop` with constructors `hyp`, `of_lam` and `of_app`;
- **AND** `#check @Stlc.Of.of_lam` shows a premise `Of (Ctx.snoc Γ T1) E T2` and the conclusion `Of Γ (Tm.lam T1 E) (Tp.arr T1 T2)`

### Requirement: Kernel-checked certificates

The command `lf_certify <sig> <name> : <query>` SHALL run the query, translate the recorded proof term into a Lean `Expr` over the exported inductives, and add it as a theorem `<name>` through the Lean kernel. The theorem's statement SHALL be the translation of the instantiated query. The theorem SHALL be added only if the kernel accepts it, and it SHALL depend on no axioms. If the kernel rejects a certificate, the command SHALL report the kernel error and add no declaration. Soundness SHALL rest only on the kernel: no answer from the engine, the LF checker or the exporter SHALL be treated as proven unless the kernel accepted its certificate.

#### Scenario: Derivation is accepted by the Lean kernel
- **WHEN** `lf_certify stlc id_typed : of (lam base x\ x) (arr base base)` runs after `lf_export stlc`
- **THEN** a theorem `id_typed : Stlc.Of Stlc.Ctx.nil (Stlc.Tm.lam Stlc.Tp.base (Stlc.Tm.var Stlc.Var.zero)) (Stlc.Tp.arr Stlc.Tp.base Stlc.Tp.base)` is added
- **AND** `#print axioms id_typed` reports that it depends on no axioms

#### Scenario: Corrupted certificate is rejected
- **WHEN** the proof term `of_lam base (x\ x) base (x\ u\ u)` is altered to `of_lam base (x\ x) (arr base base) (x\ u\ u)` and submitted through the certificate API with the LF re-check disabled
- **THEN** the Lean kernel rejects the declaration with a type-mismatch error, which the command reports
- **AND** no declaration with the requested name exists afterwards

### Requirement: Interoperation with plain programs

The system SHALL make every loaded LF signature available to plain ELPI files through type erasure:

- a family `a : Πx̄:Ā. type` SHALL become `kind a type` if it is a syntax family, and a predicate `type a |A1| -> … -> prop` if it is a judgment family;
- a constant SHALL become a constructor or clause whose simple type is the erasure of its LF type;
- an LF clause SHALL become the λProlog clause whose head is the clause's conclusion, whose premises are joined with `,`, and in which `pi x:A\` becomes `pi x\` and a hypothesis becomes `=>`.

A plain program SHALL call LF predicates and get the same answers, in the same order, as the corresponding LF query, with no proof term. The erased program SHALL be valid ELPI 1.18, and the oracle's answers on it SHALL be the reference.

#### Scenario: LF predicate is callable from a plain program
- **WHEN** a plain file accumulates `stlc` and defines `main :- of (lam base x\ lam base y\ x) T, print T.`
- **THEN** running `main` prints `arr base (arr base base)`
- **AND** running the erased `stlc` program with the same `main` on the ELPI 1.18 oracle prints the same output

### Requirement: LF search strategies

The system SHALL let an `#lf` file select a search strategy with `#strategy dfs`, `#strategy bounded <n>` or `#strategy iddfs`, and SHALL use `dfs` when none is selected:

- `dfs` SHALL be the depth-first, clause-order search of `elpi-core-engine`.
- `bounded <n>` SHALL explore the depth-first order but SHALL NOT expand any goal whose derivation depth is greater than `n`.
- `iddfs` SHALL run bounded search with increasing bounds. It SHALL report each answer exactly once, and it SHALL report finite failure only if an iteration finishes without cutting off any branch.

A strategy SHALL apply only to goals of LF families, and plain programs SHALL always use the fixed depth-first order. Every strategy SHALL record proof terms in the same way.

#### Scenario: Iterative deepening finds a proof that depth-first misses
- **WHEN** an `#lf` file declares `o : type. a : o. p : o -> type. p_loop : p X <- p X. p_a : p a.` and the query `p a` runs with `#strategy dfs` and a fuel limit of 100000 steps
- **THEN** the query fails with a fuel-exhaustion resource error
- **AND** the same query with `#strategy iddfs` succeeds, and its first answer has the proof term `p_a`
- **AND** later answers (`p_loop a p_a`, and so on) never report the proof term `p_a` again

### Requirement: Mode checking

The system SHALL accept Twelf-style mode declarations `#mode <family> <args>`, where each argument is marked `+` for input or `-` for output. These declarations SHALL be separate from ELPI's matching `mode` declarations. For each clause of a family with a mode, the system SHALL check statically that, read left to right:

- every input argument of every premise is ground, given the inputs of the head and the outputs of earlier premises;
- every output of the head is ground once all premises succeed;
- every hypothesis introduced under `pi` has ground input arguments when it is assumed.

A mode violation SHALL be reported with the clause name, the premise, the argument position and the variable that is not ground.

#### Scenario: Mode-incorrect clause is reported
- **WHEN** an `#lf` file declares `nat : type. z : nat. s : nat -> nat. plus : nat -> nat -> nat -> type. #mode plus +N +M -P.` with the clauses `plus_z : plus z M M.`, `plus_s : plus (s N) M (s P) <- plus N M P.` and `plus_bad : plus (s N) M P <- plus N K P.`
- **THEN** mode checking reports that clause `plus_bad` violates the mode: in premise `plus N K P`, input argument 2 contains `K`, which is not ground
- **AND** `plus_z` and `plus_s` raise no mode error

### Requirement: Totality checking

The system SHALL accept `#block`, `#worlds` and `#total` directives. For `#total <args> (<family> …)`, the system SHALL check mode correctness, world regularity, input coverage, output coverage and termination of the family, with termination by structural decrease of the designated arguments. A family that passes SHALL be reported as a meta-theorem: for all inputs there exist outputs. A failed check SHALL be reported with the missing case or the non-decreasing call. These checks SHALL be diagnostics outside the trust base: the system SHALL NOT add a Lean theorem for a totality claim unless the kernel accepts a proof of it. The system SHALL NOT emit `sorry` or any axiom for a claim without a proof. If no proof can be built, it MAY emit the statement as a `Prop` definition instead.

#### Scenario: Total relation is reported as a meta-theorem
- **WHEN** the `plus` signature with only `plus_z` and `plus_s` declares `#total N (plus N _ _).` and is exported to namespace `Arith`
- **THEN** the checker reports that `plus` is total in its first argument, with inputs N and M and output P
- **AND** a kernel-checked theorem `Arith.plus_total : ∀ (N M : Arith.Nat), ∃ P, Arith.Plus N M P` is added, depending on no axioms

#### Scenario: Missing case is reported by coverage
- **WHEN** the same `plus` signature without `plus_z` declares `#total N (plus N _ _).`
- **THEN** coverage checking reports the missing input case `plus z M P`
- **AND** no meta-theorem is reported and no Lean declaration named `plus_total` is added

### Requirement: Defeq bridge

The system SHALL let an `#lf` file bind an LF type to a Lean type with `#bridge <lf-type> = <LeanType>.` and an LF constant to a Lean function with `#bridge <c> : <A> = <LeanFn>.` The bridge SHALL work through the unification-hook tier of `elpi-solver-api`:

- When unification is stuck on a bridged constant applied to ground arguments, the hook SHALL evaluate the application in Lean and continue with the value as a canonical LF object.
- An application with arguments that are not ground SHALL be suspended.
- A bridged application SHALL never override a syntactic unification success.

In an exported certificate, a bridged constant SHALL be translated to the Lean function application itself, so that the kernel re-checks the computed value by definitional unfolding. A wrong bridge result SHALL therefore make the certificate fail; it SHALL NOT produce a theorem.

#### Scenario: Bridge discharges a goal by Lean computation
- **WHEN** an `#lf` file declares `#bridge nat = Nat.`, `#bridge add : nat -> nat -> nat = Nat.add.`, `same : nat -> nat -> type.` and `refl : same N N.`, and `lf_certify br five : same (add 2 3) 5` runs
- **THEN** the query succeeds with the proof term `refl (add 2 3)`, the hook having evaluated `add 2 3` to `5` while unifying the second argument
- **AND** a theorem `five : Br.Same (Nat.add 2 3) 5` is accepted by the kernel, which checks that `Nat.add 2 3` reduces to `5`
- **AND** without the two `#bridge` lines, `add` is an ordinary rigid LF constant and the query `same (add 2 3) 5` fails
