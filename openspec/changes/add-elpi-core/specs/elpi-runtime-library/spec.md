## Purpose

The Lean API that lets ordinary Lean programs use ELPI as a library: compile or load programs, run pure, IO or typed queries that return lazy solution streams, extend programs persistently and attach Lean functions as builtins.

## ADDED Requirements

### Requirement: Pure lazy queries
The library SHALL provide `Elpi.solve (p : CompiledProgram) (q : Query) : LazyList Solution`, a pure function with no `IO` in its type, whose result for the same program and query is always the same sequence of solutions in the order defined by the engine. Each `Solution` SHALL expose the bindings of the query's named variables (fully dereferenced) and any residual delayed goals. The list SHALL be lazy: forcing the first `n` elements SHALL run the machine only as far as needed to produce them, and a resource error SHALL be represented as a terminal element of the stream, distinguishable from exhaustion.

#### Scenario: Query is a pure function
- **WHEN** `Elpi.solve p q` is evaluated twice in the same Lean program for a program `p` defining `append` and the query `q := append [1] [2] L`
- **THEN** both evaluations return the single solution `L = [1, 2]`
- **AND** the expression typechecks in a pure (non-`IO`) Lean definition

#### Scenario: Only demanded solutions are computed
- **WHEN** `p` is `nat z.  nat (s N) :- nat N.` and the Lean program evaluates `(Elpi.solve p "nat X").take 3`
- **THEN** the evaluation terminates with three solutions `z`, `s z`, `s (s z)`, although the stream is infinite

### Requirement: IO queries
The library SHALL provide `Elpi.solveIO`, with the same arguments as `Elpi.solve`, which runs the query in `IO` and returns its solutions as a lazy stream in `IO`. Builtins that perform input or output (such as `print` and file-reading builtins) SHALL execute their effects in `IO`, in the order in which the search reaches them, and an engine error SHALL be raised as an `IO` exception carrying the `ElpiError` value.

#### Scenario: IO builtin is usable from solveIO
- **WHEN** a Lean `main` calls `Elpi.solveIO` on the query `print "hello", X = 1`
- **THEN** standard output receives `hello` and the first solution binds `X = 1`

### Requirement: Typed query decoding
The library SHALL provide `Elpi.solveAs [FromElpi α]`, which runs a query and decodes the bindings of its answer variables, in order of first occurrence in the query, into a Lean value of type `α`. Instances of `FromElpi` SHALL be provided for at least `Nat`, `Int`, `String`, `Bool`, `Float`, `List`, `Option`, products and ELPI terms themselves. A binding that does not have the shape required by `α` SHALL be reported as a decoding error naming the variable and the expected type, never as a silently dropped solution.

#### Scenario: Solutions decode to a Lean type
- **WHEN** a program defines `q 1 [2, 3].` and the Lean program evaluates `Elpi.solveAs (α := Nat × List Nat) p "q X Y"`
- **THEN** the result contains the single value `(1, [2, 3])`

#### Scenario: Decoding failure is reported
- **WHEN** a program defines `r "one".` and the Lean program evaluates `Elpi.solveAs (α := Nat) p "r X"`
- **THEN** the result is a decoding error that names the variable `X` and the expected type `Nat`

### Requirement: Compiled program constants
The library SHALL provide the command `elpi_program foo "<source>"` (and a file form `elpi_program foo from "path.elpi"`), which parses, typechecks and compiles the program at elaboration time and defines the constant `foo.compiled : CompiledProgram`. Parse and type errors SHALL be reported as Lean elaboration errors at the command. Using `foo.compiled` at runtime SHALL NOT invoke the parser or the typechecker.

#### Scenario: Program constant needs no parsing at runtime
- **WHEN** a module declares `elpi_program fam "parent tom bob."` and a Lean executable queries `Elpi.solve fam.compiled "parent tom X"`
- **THEN** the query yields `X = bob`
- **AND** the parser invocation counter of the runtime stays at zero for the whole run

### Requirement: Runtime program loading
The library SHALL provide `Elpi.Program.load : String → Except ElpiError CompiledProgram` and `Elpi.Program.loadFile : System.FilePath → IO (Except ElpiError CompiledProgram)`, which parse, resolve accumulations, typecheck and compile a program at runtime. Syntax errors, unresolved accumulations and type errors SHALL be returned as `ElpiError` values carrying a source position, and SHALL NOT be raised as exceptions or panics.

#### Scenario: Syntax error is returned as a value
- **WHEN** the Lean program evaluates `Elpi.Program.load "p 1"` (missing final period)
- **THEN** the result is `Except.error e` where `e` is a parse error whose position is line 1 at the end of the input

### Requirement: Persistent program extension
A `CompiledProgram` SHALL be an immutable value, and `p.assert (clause : String) : Except ElpiError CompiledProgram` SHALL return a new program equal to `p` with the clause, after parsing and typechecking against `p`'s signature, appended to the end of its predicate. The original program `p` SHALL be unchanged and remain usable, and the two programs SHALL share structure rather than copy the clause database.

#### Scenario: Asserting a clause leaves the original program unchanged
- **WHEN** `p` is `pred q o:int.  q 1.` and the Lean program builds `p' := p.assert "q 2."`
- **THEN** `Elpi.solve p "q X"` yields only `X = 1`
- **AND** `Elpi.solve p' "q X"` yields `X = 1` followed by `X = 2`

### Requirement: Runtime builtins
The library SHALL provide `p.withBuiltin "name" (sig := "pred name ...") f`, which returns a new program in which the Lean function `f` implements the predicate `name` with the given signature, without requiring an attribute or a new module. The signature SHALL be typechecked and the builtin SHALL follow the same calling convention (dereferenced inputs, lazy stream of output bindings) as attribute-registered builtins; a name clash with an existing predicate or builtin SHALL be reported as an error.

#### Scenario: Builtin attached with withBuiltin is callable
- **WHEN** the Lean program builds `p' := p.withBuiltin "double" (sig := "pred double i:int, o:int.") (fun n => [2 * n])` and evaluates `Elpi.solve p' "double 21 X"`
- **THEN** the query yields `X = 42`
