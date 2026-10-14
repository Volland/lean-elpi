## 1. LF syntax and opt-in

- [x] 1.1 Extend the parser so that a file whose first non-comment line is `#lf` is read in LF mode: `c : A.` declarations, `pi x:A\ B`, `->` and left-associative `<-`, and `#` directives. Outside LF mode these forms are parse errors.
- [x] 1.2 Add the Lean command `lf_signature <name> <file>` as sugar for accumulating an `#lf` file into a program.
- [x] 1.3 Reject plain clauses inside `#lf` files and LF directives inside plain files, with source positions.
- [x] 1.4 Annotate the LF-mode entry point in `Elpi/LF/Check.lean` with `-- @tg: implements:: [[openspec:elpi-lf#LF opt-in per file]]`.
- [x] 1.5 Write the golden test `tests/lf/OptIn.lean` (the `stlc` file with `bad`, the error position, and the query `#lf_query stlc (of (lam base x\ x) T)`). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#LF opt-in per file#lf header enables dependent checking]]`.
- [x] 1.6 Add the plain program `tests/conformance/corpus/lf_plain_size.elpi` (no header, `size` predicate) and compare it against the ELPI 1.18 oracle. Write `tests/lf/PlainUnaffected.lean`, which also checks that `#strategy` is a parse error in plain files. Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#LF opt-in per file#Plain file is unaffected]]`.

## 2. LF checker

- [x] 2.1 Define `LFType`, `LFKind`, `FamRole`, `Block`, `ModeDecl`, `TotalDecl`, `Bridge` and `LFSig` in `Elpi/LF/Check.lean`, as sketched in the design.
- [x] 2.2 Implement hereditary substitution on canonical objects, and η-expansion of user input from declared types.
- [x] 2.3 Implement the bidirectional canonical λΠ checker (K-type, K-Π, F-*, O-*) with errors that report the declaration, position, and expected and found types.
- [x] 2.4 Implement implicit-argument reconstruction (ordered by first occurrence) with ambiguity errors that name the variable.
- [x] 2.5 Infer family roles (syntax or judgment) and worlds from hypothetical premises.
- [x] 2.6 Annotate the signature checker entry point with `-- @tg: implements:: [[openspec:elpi-lf#Dependent signatures]]`.
- [x] 2.7 Write `tests/lf/IllTyped.lean` (`bad2 : of (lam base base) base.`, with no constant added). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Dependent signatures#Ill-typed LF object is rejected]]`.
- [x] 2.8 Write `tests/lf/IndexedFamily.lean` (`vec`, the reconstructed type of `vcons`, `wrong` accepted, `wrong2` rejected). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Dependent signatures#Type family is indexed by objects]]`.

## 3. Unification and proof-term recording

- [x] 3.1 Implement elaboration of LF clauses into internal `lf.<fam>` predicates that take the proof term as an extra first argument, with `pi` and hypothesis premises applying the body hole to the eigenvariables (`Elpi/LF/ProofTerm.lean`).
- [x] 3.2 Keep implicit arguments explicit in elaborated terms. Route LF unification through the unchanged core pattern unifier, so that non-pattern problems become delayed goals.
- [x] 3.3 Implement zonking of the root hole into `ProofTerm`, the `Certificate` structure with `residue`, and a refusal to certify while `residue` is non-empty.
- [x] 3.4 Add `#lf_query` output that prints the answer substitution and the fully explicit proof term, plus the CLI flag `--lf-proof`.
- [x] 3.5 Annotate the LF unification entry point (the elaborated-goal unify call) with `-- @tg: implements:: [[openspec:elpi-lf#Pattern unification for LF]]`.
- [x] 3.6 Annotate the elaborator and zonker in `Elpi/LF/ProofTerm.lean` with `-- @tg: implements:: [[openspec:elpi-lf#Proof term recording]]`.
- [x] 3.7 Write `tests/lf/PatternUnif.lean` (`lam base (y\ app y y)` fails finitely; `q G` reports the residual `G (app c c) = c` and refuses certification). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Pattern unification for LF#LF unification stays in the pattern fragment]]`.
- [x] 3.8 Write `tests/lf/ProofTerm.lean` (the proof term `of_lam base (x\ x) base (x\ u\ u)`, which the LF checker re-checks). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Proof term recording#Successful query yields a derivation term]]`.

## 4. Interoperation by erasure

- [x] 4.1 Implement type erasure of signatures and clauses, and generate the plain wrapper `fam A1 … An :- lf.fam _ A1 … An` for each judgment family.
- [x] 4.2 Implement `lean-elpi --lf-erase`, which writes the erased program (without proof arguments) as a valid ELPI 1.18 file.
- [x] 4.3 Annotate the erasure function with `-- @tg: implements:: [[openspec:elpi-lf#Interoperation with plain programs]]`.
- [x] 4.4 Add `tests/conformance/corpus/lf_stlc_erased.elpi` (the erased `stlc` plus `main`) and compare it against the ELPI 1.18 oracle. Write `tests/lf/Interop.lean`, in which a plain file accumulates `stlc` and prints `arr base (arr base base)`. Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Interoperation with plain programs#LF predicate is callable from a plain program]]`.

## 5. Export to Lean inductive families

- [x] 5.1 Generate `Var`, scope-indexed syntax inductives (`Tm : Nat → Type`, and `List Srt` scopes for several bindable sorts), and binder-free syntax inductives (`Tp`) in `Elpi/LF/Export.lean`.
- [x] 5.2 Generate `Ctx` from worlds (`snoc` for a single block), the `Ctx.Lookup` relation, and judgment inductives in `Prop` with lookup constructors and context-extending premises.
- [ ] 5.3 Generate structurally recursive `Tm.ren`, `Tm.subst` and `Tm.inst` for non-pattern instances in constructor types. Use `Nat.succ` only, with no `Fin`, numerals or instances. Not done in this change: non-pattern instances in constructor types are rejected by the fragment check instead of being translated with `Tm.ren`/`Tm.subst`.
- [x] 5.4 Check the exportable fragment and reject declarations outside it, naming them, before any `addDecl`.
- [ ] 5.5 Implement the `lf_export` command, which prints the generated declarations and caches them by signature hash in an environment extension. Support `#export <fam> : Type` overrides. Partly done: `lf_export` generates and elaborates the declarations; the signature-hash cache and `#export <fam> : Type` overrides are not implemented.
- [x] 5.6 Implement the object and derivation translation `⌜·⌝` (level to index, binder stripping, context extension, lookup chains) to `Expr`.
- [x] 5.7 Annotate the inductive generator with `-- @tg: implements:: [[openspec:elpi-lf#Lean inductive export]]`.
- [x] 5.8 Write `tests/lf/Export.lean` (`#check` of `Stlc.Tm`, `Stlc.Of` and `@Stlc.Of.of_lam`, with golden output). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Lean inductive export#Type family compiles to an inductive family]]`.
- [ ] 5.9 Add round-trip property tests (LF canonical object → Lean value → LF object) for the syntax part of the adequacy theorem. Not done in this change: no round-trip property tests; the encoding is covered by the export and certificate tests.

## 6. Kernel-checked certificates

- [x] 6.1 Implement `lf_certify <sig> <name> : <query>`: search, zonk, optional LF re-check, ensure export, build the `type` and `value` Exprs, run `Meta.check`, then `addDecl (.thmDecl …)`. Done without `Meta.check`: the kernel alone decides.
- [x] 6.2 Refuse to certify when kernel checking is disabled (`debug.skipKernelTC`). Report kernel errors verbatim, and add no declaration on rejection.
- [x] 6.3 Expose a certificate API that accepts a given proof term, with the LF re-check switchable, for testing the trust boundary.
- [x] 6.4 Annotate the certification function in `Elpi/LF/Export.lean` with `-- @tg: implements:: [[openspec:elpi-lf#Kernel-checked certificates]]`.
- [x] 6.5 Write `tests/lf/CertifyOk.lean` (`lf_certify stlc id_typed …`, the exact theorem type, and `#print axioms` reporting no axioms). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Kernel-checked certificates#Derivation is accepted by the Lean kernel]]`.
- [x] 6.6 Write `tests/lf/CertifyCorrupt.lean` (the altered `of_lam … (arr base base) …` with the re-check off, the kernel error, and no declaration). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Kernel-checked certificates#Corrupted certificate is rejected]]`.

## 7. LF search strategies

- [x] 7.1 Define `Strategy` with `dfs`, `bounded` and `iddfs` in `Elpi/LF/Strategy.lean`.
- [x] 7.2 Add a per-goal-frame derivation depth and a per-run `cutoff` flag to the machine, consulted only for LF goals. Add the restart driver with shared fuel.
- [x] 7.3 Parse `#strategy dfs | bounded <n> | iddfs`, and filter answers by proof-height window to avoid duplicates.
- [x] 7.4 Annotate the strategy driver with `-- @tg: implements:: [[openspec:elpi-lf#LF search strategies]]`.
- [x] 7.5 Write `tests/lf/Strategies.lean` (`p_loop` and `p_a`: depth-first runs out of fuel; `iddfs` gives the first answer `p_a`, never repeated). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#LF search strategies#Iterative deepening finds a proof that depth-first misses]]`.

## 8. Mode checking

- [x] 8.1 Parse `#mode <fam> <±args>` as a separate declaration from ELPI's `mode`.
- [x] 8.2 Implement groundness abstract interpretation over clauses, covering premises left to right, eigenvariables, hypotheses and strict pattern occurrences, with errors that name the clause, premise, argument and variable.
- [x] 8.3 Annotate the mode checker with `-- @tg: implements:: [[openspec:elpi-lf#Mode checking]]`.
- [x] 8.4 Write `tests/lf/Modes.lean` (`plus_bad` is reported with `K`; `plus_z` and `plus_s` are clean). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Mode checking#Mode-incorrect clause is reported]]`.

## 9. Totality: worlds, termination and coverage

- [x] 9.1 Parse `#block`, `#worlds` and `#total`, and implement the world-regularity check.
- [x] 9.2 Implement the structural and lexicographic termination check, including higher-order subterms.
- [x] 9.3 Implement input and output coverage by splitting, reporting missing cases such as `plus z M P`.
- [x] 9.4 Build the totality proof as an `Expr` for single-argument structural recursion and submit it through the kernel. Otherwise emit only a `Prop` statement definition. Never emit `sorry` or axioms. Done with a tactic proof (structural induction, elaborated through the kernel) instead of a hand-built `Expr`; when no proof can be built nothing is added.
- [x] 9.5 Annotate the totality checker with `-- @tg: implements:: [[openspec:elpi-lf#Totality checking]]`.
- [x] 9.6 Write `tests/lf/TotalOk.lean` (`Arith.plus_total : ∀ N M, ∃ P, Arith.Plus N M P`, kernel-checked, no axioms). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Totality checking#Total relation is reported as a meta-theorem]]`.
- [x] 9.7 Write `tests/lf/TotalCoverage.lean` (`plus_z` removed: the missing case is reported and no `plus_total` exists). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Totality checking#Missing case is reported by coverage]]`.

## 10. Defeq bridge

- [x] 10.1 Parse `#bridge <ty> = <LeanType>.` and `#bridge <c> : <A> = <LeanFn>.`, and register bridged heads as *defined* heads that the unifier treats as stuck.
- [x] 10.2 Implement the bridge as a unification hook in the solver registry: ground arguments are evaluated in MetaM and marshalled back through `ToElpi`/`FromElpi`; arguments that are not ground are delayed. A clear error is raised without a Lean environment.
- [x] 10.3 Translate bridged constants in certificates to the Lean function application.
- [x] 10.4 Annotate the bridge hook with `-- @tg: implements:: [[openspec:elpi-lf#Defeq bridge]]`.
- [x] 10.5 Write `tests/lf/Bridge.lean` (`same (add 2 3) 5`: the proof term `refl (add 2 3)` and the kernel-checked theorem `five`; without the bridge the query fails). Annotate it with `-- @tg: verifies:: [[openspec:elpi-lf#Defeq bridge#Bridge discharges a goal by Lean computation]]`.

## 11. Docs and traceability

- [x] 11.1 Write or update `tg.md/papers/certified-lf.md` ("Certified Proof Search with LF"). It should cover the surface syntax, proof holes, the export encoding with the adequacy statement, the trust boundary, strategies and the bridge. Set its frontmatter to `openspec: [elpi-lf]`, and name the requirements in prose as `elpi-lf › <Requirement>`.
- [x] 11.2 Update `tg.md/changes.md#add-elpi-lf` and `tg.md/architecture/uml.md#LF certification sequence` to match this design. Check that the components `LF checker`, `LF proof terms`, `LF export` and `LF strategies` point to their modules.
- [x] 11.3 Propose the new Decisions from `design.md` ("LF surface syntax", "Proof holes by elaboration", "Well-scoped export with explicit contexts", "No unproved totality theorems") as sections in `tg.md/decisions.md`, or record them under `LF as the dependent extension`.
- [x] 11.4 Run `tg check` and `tg trace elpi-lf --gaps`. Close every reported gap: each requirement needs an `implements` annotation and each scenario a `verifies` annotation, and every link must resolve.
