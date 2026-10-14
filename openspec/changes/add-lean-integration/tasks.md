## 1. Expr reflection

- [ ] 1.1 Create `Elpi/Lean/Reflect.lean` with `ReflectCtx` (pointer cache, binder stack, level interner) and the ctypes `name`, `binder`, `level`, `literal`, `mvarid`, `fvarid` and `mdata` (design D2)
- [ ] 1.2 Implement `Reflect.toTerm` for every `Expr` form except `bvar`: `app` spines, λ-abstractions for binders, and an error on loose `bvar` (design D1, D3)
- [ ] 1.3 Implement `Reflect.ofTerm` with a binder stack of fresh fvars, `mkLambdaFVars`/`mkForallFVars`/`mkLetFVars`, and optional conversion of leftover ELPI variables to metavariables
- [ ] 1.4 Intern levels so structurally equal levels share a handle, and make handle unification compare identities
- [ ] 1.5 Annotate the `term` constructors' registration with `-- @tg: implements:: [[openspec:lean-reflection#HOAS term encoding]]`
- [ ] 1.6 Annotate `Reflect.ofTerm` with `-- @tg: implements:: [[openspec:lean-reflection#Lossless Expr round trip]]`
- [ ] 1.7 Annotate the level interner with `-- @tg: implements:: [[openspec:lean-reflection#Opaque universe levels]]`

## 2. Marshalling, deriving, quotations

- [ ] 2.1 Create `Elpi/Lean/Marshal.lean` with `ToElpi`/`FromElpi`, the structured `DecodeError`, and instances for `Nat`, `Int` (range-checked), `String`, `Bool`, `Float`, `Name`, `Expr`, `Level`, `List`, `Option`, `Prod` and `Array`
- [ ] 2.2 Implement the `deriving Elpi` handler: instances plus `kind`/`type` declarations (inductive constructors use their short names, a structure gets `<kind>.mk`), with errors for missing field instances and name clashes. Register the declarations in `elpiExt`
- [ ] 2.3 Implement the quotation pass in the ELPI parser: `{{ t }}` handed to the Lean term parser with mapped positions, `lp:{{X}}` replaced by synthetic holes, holes abstracted to ELPI variables, and the result stored reflected (design D6)
- [ ] 2.4 Annotate `ToElpi`/`FromElpi` with `-- @tg: implements:: [[openspec:lean-reflection#Typed marshalling classes]]`
- [ ] 2.5 Annotate the deriving handler with `-- @tg: implements:: [[openspec:lean-reflection#Deriving Elpi]]`
- [ ] 2.6 Annotate the quotation elaborator with `-- @tg: implements:: [[openspec:lean-reflection#Quotations]]`

## 3. Environment extension and commands

- [ ] 3.1 Create `Elpi/Lean/Commands.lean` with `elpiExt : SimplePersistentEnvExtension` and the entries `declProgram`, `declDb`, `accumulate`, `deriveDecls` and `export`, replayed in import order (design D4)
- [ ] 3.2 Make `CompiledUnit` serialisable: indexed clauses, signatures and the source map
- [ ] 3.3 Implement `elpi_program`, `elpi_db` and `elpi_accumulate T (file "…" | db D | lp%{ … }%)`, with parsing and type checking done when the module is compiled
- [ ] 3.4 Implement position mapping from `lp%{ … }%` token positions (code-point arithmetic over the `FileMap`) into `logErrorAt` (design D5)
- [ ] 3.5 Implement `#elpi P lp%{ Q }%`, showing bindings pretty-printed with `ppExpr` and residual constraints, honouring the `elpi.solutions` option, and distinguishing "no solution" from fuel errors
- [ ] 3.6 Implement `elpi_command name := P` (running `main Args` in `CommandElabM`) and `elpi_export name` (generated `syntax` + `elab_rules`) (design D9)
- [ ] 3.7 Annotate `elpiExt` with `-- @tg: implements:: [[openspec:lean-integration#Program and database declarations]]`
- [ ] 3.8 Annotate the `elpi_accumulate` elaborator with `-- @tg: implements:: [[openspec:lean-integration#Source accumulation]]`
- [ ] 3.9 Annotate the `#elpi` elaborator with `-- @tg: implements:: [[openspec:lean-integration#Query command]]`
- [ ] 3.10 Annotate the `elpi_command`/`elpi_export` elaborators with `-- @tg: implements:: [[openspec:lean-integration#ELPI commands and export]]`

## 4. MetaM instance, builtins, tactics, phases

- [ ] 4.1 Give `MetaM` a `Backtrackable` instance with lazily saved `Meta.SavedState` (host epoch) for choice points
- [ ] 4.2 Create `Elpi/Lean/Builtins.lean` with `lean.env.find`, `lean.infer`, `lean.whnf`, `lean.defeq`, `lean.elab`, `lean.mk_mvar`, `lean.pp`, `lean.add_decl`, `lean.db.accumulate` and `lean.last-error`, where exceptions become failure plus the recorded message
- [ ] 4.3 Add `ExecCtx.phase` and `requires : Option Phase` to registry entries, and check them in the machine before each builtin call (design D8)
- [ ] 4.4 Create `Elpi/Lean/Tactic.lean`: `elpi_tactic name := P`, the `by elpi name args` syntax, argument encoding (`int`/`str`/`trm`), goal reflection, the call to `solve`, reification, the `isDefEq` check, assignment and the new goals (design D7)
- [ ] 4.5 Implement `Elpi.query (p : Elpi.Program) (q : Elpi.Query) : MetaM (LazyList Solution)` with a `String` coercion for queries
- [ ] 4.6 Annotate the tactic bridge entry with `-- @tg: implements:: [[openspec:lean-integration#ELPI tactics]]`
- [ ] 4.7 Annotate the builtin table with `-- @tg: implements:: [[openspec:lean-integration#Lean builtins]]`
- [ ] 4.8 Annotate the phase check with `-- @tg: implements:: [[openspec:lean-integration#Phase-restricted effects]]`
- [ ] 4.9 Annotate `Elpi.query` with `-- @tg: implements:: [[openspec:lean-integration#Programmatic meta API]]`

## 5. Runtime rule DSL and ELPI libraries

- [ ] 5.1 Create `Elpi/Runtime/Dsl.lean`: the `elpi_rules name where …` syntax, the Lean-type to ELPI-type map from `deriving Elpi`, compile-time type checking with Lean positions, and the outputs `name.compiled` and `name.p` query helpers
- [ ] 5.2 Write `lib/elpi/lean.elpi`: the reflection types, `goal`/`decl`/`argument`, builtin signatures generated from the registry, and `copy`, `lean.mk_app` and `lean.subst`. Add a test that the signatures match the registry
- [ ] 5.3 Write `lib/elpi/lean.ltac.elpi`: `tactic` and the `intro`, `exact`, `apply`, `refine`, `assumption`, `then`, `thenl`, `orelse`, `try`, `repeat` and `focus` tactics under the `lean.ltac.` namespace
- [ ] 5.4 Write `lib/elpi/lean.derive.elpi` (BEq, DecidableEq and Repr derivers) and the exported command `elpi_derive <Class> <Type>`
- [ ] 5.5 Register the three libraries with `Elpi/Lean/Libraries.lean` (search the `lib/elpi/` folder of every Lake package, embedded in the binary)
- [ ] 5.6 Annotate `elpi_rules` with `-- @tg: implements:: [[openspec:elpi-runtime-library#Typed rule DSL]]`
- [ ] 5.7 Annotate `lib/elpi/lean.elpi` with `% @tg: implements:: [[openspec:elpi-libraries#Lean API library]]`
- [ ] 5.8 Annotate `lib/elpi/lean.ltac.elpi` with `% @tg: implements:: [[openspec:elpi-libraries#Tactic combinator library]]`
- [ ] 5.9 Annotate `lib/elpi/lean.derive.elpi` with `% @tg: implements:: [[openspec:elpi-libraries#Derive library]]`

## 6. Tests (one per scenario, `#guard_msgs` golden tests)

- [ ] 6.1 `tests/Lean/Reflect.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#HOAS term encoding#Lean binder becomes an ELPI lambda]]`
- [ ] 6.2 `tests/Lean/Reflect.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#HOAS term encoding#Constructors cover every Expr form]]`
- [ ] 6.3 `tests/Lean/RoundTrip.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Lossless Expr round trip#Round trip preserves universe levels]]`
- [ ] 6.4 `tests/Lean/RoundTrip.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Lossless Expr round trip#Round trip preserves metadata and projections]]`
- [ ] 6.5 `tests/Lean/Levels.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Opaque universe levels#Levels compare by handle identity]]`
- [ ] 6.6 `tests/Lean/Marshal.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Typed marshalling classes#Nat round-trips through ToElpi and FromElpi]]`
- [ ] 6.7 `tests/Lean/Marshal.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Typed marshalling classes#Decoding a wrong shape fails]]`
- [ ] 6.8 `tests/Lean/Derive.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Deriving Elpi#Inductive emits kind and type declarations]]`
- [ ] 6.9 `tests/Lean/Derive.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Deriving Elpi#Structure emits a constructor declaration]]`
- [ ] 6.10 `tests/Lean/Quotation.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Quotations#Quotation elaborates to a term]]`
- [ ] 6.11 `tests/Lean/Quotation.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-reflection#Quotations#Antiquotation splices an ELPI variable]]`
- [ ] 6.12 `tests/Lean/Program/A.lean` + `tests/Lean/Program/B.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Program and database declarations#Program persists across imports]]`
- [ ] 6.13 `tests/Lean/Program/B.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Program and database declarations#Database extended downstream]]`
- [ ] 6.14 `tests/Lean/Accumulate.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Source accumulation#Inline source error maps to the Lean position]]`
- [ ] 6.15 `tests/Lean/Accumulate.lean` (+ `tests/Lean/rules.elpi`): write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Source accumulation#File accumulation]]`
- [ ] 6.16 `tests/Lean/Query.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Query command#Solutions are shown in the infoview]]`
- [ ] 6.17 `tests/Lean/Query.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Query command#Failure is reported]]`
- [ ] 6.18 `tests/Lean/Tactic.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#solve assigns the goal metavariable]]`
- [ ] 6.19 `tests/Lean/Tactic.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#Ill-typed proof is rejected]]`
- [ ] 6.20 `tests/Lean/Tactic.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#ELPI tactics#Remaining goals are returned to Lean]]`
- [ ] 6.21 `tests/Lean/Command.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#ELPI commands and export#Exported command parses its arguments]]`
- [ ] 6.22 `tests/Lean/Builtins.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Lean builtins#lean.infer returns the type]]`
- [ ] 6.23 `tests/Lean/Builtins.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Lean builtins#lean.defeq decides definitional equality]]`
- [ ] 6.24 `tests/Lean/Phase.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Phase-restricted effects#Declaration added from a tactic is rejected]]`
- [ ] 6.25 `tests/Lean/MetaApi.lean`: write the test and add `-- @tg: verifies:: [[openspec:lean-integration#Programmatic meta API#Elpi.query is usable from MetaM]]`
- [ ] 6.26 `tests/Runtime/Dsl.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed rule DSL#Ill-typed rule is rejected at compile time]]`
- [ ] 6.27 `tests/Runtime/Dsl.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-runtime-library#Typed rule DSL#Rules compile to a program constant]]`
- [ ] 6.28 `tests/Libraries/Lean.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-libraries#Lean API library#lean library declares the term type]]`
- [ ] 6.29 `tests/Libraries/Ltac.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-libraries#Tactic combinator library#then composes two tactics]]`
- [ ] 6.30 `tests/Libraries/Ltac.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-libraries#Tactic combinator library#orelse falls back on failure]]`
- [ ] 6.31 `tests/Libraries/Derive.lean`: write the test and add `-- @tg: verifies:: [[openspec:elpi-libraries#Derive library#Derived BEq instance is accepted by Lean]]`
- [ ] 6.32 Property test: round trip over every declaration type and value in `Init` (`Expr.equal` after reflect followed by reify)
- [ ] 6.33 Position-mapping golden tests with tabs, CRLF and non-ASCII identifiers in `lp%{ … }%`

## 7. Conformance (ELPI 1.18-defined behaviour)

- [ ] 7.1 Add `tests/conformance/corpus/lean/ltac_shapes.elpi`: the parts of the `lean.ltac` combinators that are plain ELPI, run with stubbed builtins, comparing control flow (`orelse` with no choice point, `repeat`, `thenl` arity) against the oracle
- [ ] 7.2 Add `tests/conformance/corpus/lean/copy.elpi`: the `copy` helper on an ELPI-declared mirror of `term` with no `lean.*` builtins, compared against the oracle
- [ ] 7.3 Run the harness against `elpi` 1.18, and register divergences that cannot be fixed (programs that need `lean.*` builtins are excluded and listed as Lean-only)

## 8. Knowledge graph and docs

- [ ] 8.1 Update the [[changes#add-lean-integration]] section and the components [[components#Expr reflection]], [[components#Marshalling]], [[components#Lean builtins]], [[components#Commands]], [[components#Tactic bridge]] and [[components#Rule DSL]] with `introduced_by`/`depends_on` edges
- [ ] 8.2 Add `openspec: [lean-reflection, lean-integration, elpi-runtime-library, elpi-libraries]` to the frontmatter of `tg.md/papers/lean-together.md` and `tg.md/papers/type-bridge.md`, and name the requirements in prose (for example `lean-integration › ELPI tactics`)
- [ ] 8.3 Check that [[uml#Tactic sequence]] and [[uml#Query sequence]] match design D7 and D4

## 9. Verification

- [ ] 9.1 Run `openspec validate add-lean-integration --strict`
- [ ] 9.2 Run `tg check` and fix every broken link, code ref and annotation
- [ ] 9.3 Run `tg trace lean-reflection lean-integration elpi-runtime-library elpi-libraries --gaps` and close every gap it reports
