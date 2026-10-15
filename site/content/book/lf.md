---
title: Certified proof search with LF
order: 10
summary: The LF layer: signatures, proof terms, export to Lean, and kernel-checked certificates.
---
# Certified proof search with LF

The LF layer turns the engine into a proof searcher whose answers the Lean kernel checks. The search engine can be wrong; the certificate cannot be.

## Judgments as types

In the Edinburgh Logical Framework (LF), a judgment such as "term E has type T" is a **type** `of E T`, each inference rule is a **constant**, and a derivation is a **term**. So a derivation found by search is an object that can be checked.

Opt in with a first line `#lf`. Here is the simply typed λ-calculus:

```elpi
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

Declarations are `c : A.` Π is `pi x:A\ B`. `A -> B` is the arrow, and `B <- A` means the same thing read backwards. Uppercase variables are implicitly bound and their types are reconstructed. The checker rejects ill-typed signatures with a position, the expected type, and the found type.

## Queries and proof terms

```bash
lean-elpi --lf-proof 'of (lam base x\ x) T' stlc.elpi
```

```text
T = arr base base
proof: of_lam base (x0\ x0) base (x0\ x1\ x1)
```

The proof term lists the rule used with its implicit arguments, followed by the proofs of its premises. A hypothetical premise becomes a λ over the new variable and the new hypothesis.

Inside Lean:

```lean
lf_signature stlc "stlc.elpi"
#lf_query stlc lp%{ of (lam base x\ x) T }%
```

## Export and certificates

```lean
lf_export stlc
lf_certify stlc id_typed lp%{ of (lam base x\ x) (arr base base) }%
#print axioms id_typed   -- does not depend on any axioms
```

`lf_export` generates Lean declarations in the namespace `Stlc`: an inductive `Tp`; a scope-indexed `Tm : Nat → Type` built on a variable type `Var`; a context `Ctx`; a lookup relation for hypotheses; and `Of : Ctx n → Tm n → Tp → Prop` with one constructor per rule. `lf_certify` runs the query, translates the proof term to a Lean term, and asks the kernel to accept the theorem

```lean
theorem id_typed : Stlc.Of Stlc.Ctx.nil
  (Stlc.Tm.lam Stlc.Tp.base (Stlc.Tm.var Stlc.Var.zero)) (Stlc.Tp.base.arr Stlc.Tp.base)
```

If the kernel rejects a certificate, the command reports its error and adds nothing. Soundness rests on the kernel alone.

## Search strategies

By default the search is depth-first. Directives choose another: `#strategy bounded 5`, or `#strategy iddfs` for iterative deepening, which finds a proof that depth-first misses when a recursive rule comes first and reports each answer once.

## Modes, totality and the bridge

- `#mode plus +N +M -P.` checks, clause by clause, that inputs are ground when used. A violation names the clause, premise, argument and variable.
- `#total N (plus N _ _).` checks coverage and termination. If the claim passes, `lf_export` also adds a theorem such as `Arith.plus_total : ∀ (N M : Arith.Nat), ∃ P, Arith.Plus N M P`, proved by structural induction and checked by the kernel. If a case is missing, you get the missing case, such as `plus z M P`, and no theorem.
- `#bridge nat = Nat.` and `#bridge add : nat -> nat -> nat = Nat.add.` let unification discharge `same (add 2 3) 5` by Lean computation. The exported theorem mentions `Nat.add 2 3`, so the kernel re-checks the value.

## Using LF signatures from plain programs

Any `#lf` file accumulated into a plain program is erased to ordinary ELPI types and clauses (`--lf-erase` prints the result). Plain programs then call `of` and get the same answers, without proof terms.

## Limits of this release

The exporter covers one assumption family and binders over the family being defined. Totality theorems are built for a single designated argument. Bridged functions return `Nat`. These are listed in the repository's LF paper.
