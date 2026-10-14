---
type: Concept
status: stable
---
# Glossary

Domain terms with one exact meaning in this project. Every paper, spec and decision uses these words in exactly this sense.

The `defines::` edge on each term points at the component where the concept is realised in code.

## Lambda Prolog

A higher-order logic programming language by Miller and Nadathur, based on hereditary Harrop formulas, with λ-terms as data and higher-order unification.

It extends Prolog with typed λ-terms, universal goals (`pi x\ G`) and implication goals (`D => G`), which makes it a natural language for manipulating syntax with binders.

- defines:: [[components#Abstract machine]]

## ELPI

An extension of λProlog by Dunchev, Guidi, Sacerdoti Coen and Tassi, implemented in OCaml, adding constraints, CHR, modes, spilling and clause grafting.

ELPI is the embedded logic language of Coq-Elpi. LeanElpi reimplements the ELPI 1.18 dialect in Lean: see [[decisions#ELPI 1.18 dialect]].

- defines:: [[components#Parser]]

## Hereditary Harrop formula

The class of logical formulas λProlog programs and goals are made of: Horn clauses extended with universal quantification and implication in goals.

A goal `pi x\ G` introduces an [[glossary#Eigenvariable]]; a goal `D => G` proves `G` with clause `D` temporarily added to the program.

- defines:: [[components#Abstract machine]]

## HOAS

Higher-order abstract syntax: representing object-language binders with the meta-language's own λ, so substitution and α-equivalence come for free.

Lean's `fun x => b` is reflected as the ELPI term `fun N Ty (x\ B)`, so ELPI's own binder represents Lean's. See [[decisions#Plain types with reflected Lean terms]].

- defines:: [[components#Expr reflection]]

## Unification variable

A logic variable (uvar) that unification may instantiate; in LeanElpi each uvar records the scope level at which it was created.

The scope level says which [[glossary#Eigenvariable]]s the variable may depend on; pattern unification uses it to prune and to check scope.

- defines:: [[components#Term store]]

## Pattern fragment

Miller's decidable fragment of higher-order unification: a uvar applied to distinct bound variables, such as `X a b` with `a`, `b` distinct eigenvariables.

Inside the fragment unification has most general unifiers ([[constraints#Pattern unification is decidable]]); outside it, LeanElpi suspends the problem as a [[glossary#Delayed goal]].

- defines:: [[components#Unifier]]

## Eigenvariable

A fresh constant introduced by a universal goal `pi x\ G`; it stands for an arbitrary term and cannot be instantiated.

Unification variables created before the eigenvariable may not depend on it; scope levels enforce this.

- defines:: [[components#Abstract machine]]

## Choice point

A record of an untried alternative: the remaining clauses, the goal stack, the store version and the host-monad snapshot to restore on backtracking.

Because the store is persistent, restoring a choice point is just reinstating the saved values: [[decisions#Persistent store]].

- defines:: [[components#Abstract machine]]

## Cut

The `!` goal, which commits to the current clause and removes the choice points created since the predicate was called.

LeanElpi implements cut with cut barriers on the choice-point stack, so cut never escapes the predicate call that contains it.

- defines:: [[components#Abstract machine]]

## Spilling

ELPI's `{p X}` syntax inside a term: it calls predicate `p` before the enclosing goal and substitutes its last output argument for the braces.

For example `print {calc (1 + 2)}` first solves `calc (1 + 2) R`, then runs `print R`.

- defines:: [[components#Parser]]

## Clause grafting

Naming a clause with `:name "n"` and inserting new clauses relative to it with `:before "n"` or `:after "n"`.

Grafting lets a Lean database or a later file extend a program at a precise position, which matters because clause order is answer order.

- defines:: [[components#Clause index]]

## Delayed goal

A goal suspended on unassigned unification variables with `declare_constraint`, resumed as soon as one of them is instantiated.

Delayed goals are the base mechanism for [[glossary#Constraint Handling Rules]] and for problems outside the [[glossary#Pattern fragment]].

- defines:: [[components#Constraint store]]

## Constraint Handling Rules

CHR: a rule language that rewrites the store of delayed goals; simplification rules remove constraints, propagation rules add new ones.

In ELPI a rule lists kept constraints, then `\` and removed constraints, an optional `|` guard, and `<=>` the goal to run. It is solver tier T1: [[decisions#Tiered solver API]].

- defines:: [[components#CHR engine]]

## Builtin predicate

A predicate whose body is a Lean function, declared with an ELPI signature and registered with `@[elpi_builtin]` or `withBuiltin`.

Builtins run in the [[glossary#Host monad]], so under `MetaM` they can infer types and check definitional equality. They are solver tier T2.

- defines:: [[components#Solver registry]]

## Constraint handler

A Lean object that owns some constraint keys, simplifies or propagates when such constraints are added, and wakes when a watched variable is instantiated.

Its state lives in the persistent constraint store, so it backtracks with the search. It is solver tier T3.

- defines:: [[components#Constraint store]]

## Unification hook

A Lean function consulted only when syntactic and pattern unification are stuck; it may solve, suspend or fail but never overrides a syntactic success.

Hooks provide equational theories such as AC and the optional defeq bridge for LF. They are solver tier T4.

- defines:: [[components#Unifier]]

## Reflection

The translation between `Lean.Expr` and the ELPI `term` datatype, in both directions and without loss.

See [[decisions#Lossless reflection with opaque levels]].

- defines:: [[components#Expr reflection]]

## Marshalling

Typed conversion of ordinary Lean values (numbers, strings, lists, user inductives) to ELPI terms and back through `ToElpi` and `FromElpi`.

`deriving Elpi` generates both instances plus the ELPI `kind`/`type` declarations of the type.

- defines:: [[components#Marshalling]]

## LF

The Edinburgh Logical Framework (λΠ): dependent function types and type families with only β and η, no computation in types.

LeanElpi uses LF as the object theory of its opt-in dependent layer: [[decisions#LF as the dependent extension]].

- defines:: [[components#LF checker]]

## Proof term

An LF object recorded during search that witnesses how a query was derived, one constructor per clause used.

In the LF layer every successful query yields a proof term; exported to Lean it becomes a [[glossary#Certificate]].

- defines:: [[components#LF proof terms]]

## Certificate

A Lean term, built from an exported proof term, whose type is the Lean statement of the query; the Lean kernel checks it.

Certificates move trust from the ELPI engine to the kernel: [[constraints#Kernel is the trust anchor]].

- defines:: [[components#LF export]]

## Oracle

The upstream OCaml `elpi` 1.18 binary, used only in tests: its answers, in order, are the reference that LeanElpi must reproduce.

See [[constraints#Oracle is ELPI 1.18]].

- defines:: [[components#Conformance harness]]

## Host monad

The monad the engine runs in, with `Backtrackable` save and restore: a light state monad for the CLI and library, `MetaM` inside Lean.

Choice points capture host-monad snapshots, so effects made by builtins are undone on backtracking.

- defines:: [[components#Abstract machine]]

## Fuel

A bound on the number of machine steps a query may take; running out yields a resource error instead of looping forever.

Under `MetaM` fuel is checked alongside Lean's heartbeats.

- defines:: [[components#Abstract machine]]

## Phase restriction

The rule that builtins changing the Lean environment (`lean.add_decl`, `lean.db.accumulate`) run only under ELPI commands, never inside tactics or term elaboration.

The engine enforces it with a capability flag set by the entry point that started the query.

- defines:: [[components#Lean builtins]]
