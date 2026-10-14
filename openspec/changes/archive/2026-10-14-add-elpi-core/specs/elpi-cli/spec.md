## Purpose

The standalone `lean-elpi` command-line tool and precompiled ELPI executables: run ELPI programs with flags compatible with the upstream `elpi` 1.18 binary, optionally inside a Lean environment, interactively through a REPL, or as native executables generated with `elpi_main`.

## ADDED Requirements

### Requirement: Upstream-compatible command line
The `lean-elpi` binary SHALL accept `lean-elpi FILE... [-exec PRED] [-test] [-I DIR]... [-- ARGS...]` with the meaning of the ELPI 1.18 flags: the files are loaded as one program; `-exec PRED` runs the predicate `PRED` with the list of strings `ARGS` given after `--` as its single argument; `-test` runs the predicate `main` and reports the outcome. The exit status SHALL be 0 when the executed query succeeds and non-zero when it fails or an error occurs. Load errors SHALL be printed to standard error with source positions. For every flag combination the oracle also accepts, the observable output (excluding timing figures) and exit status of the oracle are the reference.

#### Scenario: Exec runs a predicate with arguments
- **WHEN** `hello.elpi` contains `main [A, B] :- print A B.` and the command `lean-elpi hello.elpi -exec main -- foo bar` is run
- **THEN** standard output receives `foo bar` and the exit status is 0
- **AND** running `lean-elpi hello.elpi -exec main -- foo` exits with a non-zero status because `main` fails

#### Scenario: Test flag runs the main predicate
- **WHEN** `t.elpi` contains `main :- 1 < 2.` and the command `lean-elpi t.elpi -test` is run
- **THEN** the output reports success as the oracle does and the exit status is 0
- **AND** when `main` is `main :- 2 < 1.` the output reports failure and the exit status is non-zero

### Requirement: Include paths
Every `-I DIR` option SHALL add `DIR` to the include paths used to resolve `accumulate` directives, in the order given on the command line, ahead of Lake package directories and embedded libraries.

#### Scenario: Include path resolves accumulate
- **WHEN** `libs/util.elpi` defines `util 7.`, `main.elpi` contains `accumulate util.  main :- util X, print X.`, and the command `lean-elpi -I libs main.elpi -exec main` is run from a directory that does not contain `util.elpi`
- **THEN** the accumulation resolves to `libs/util.elpi`, standard output receives `7` and the exit status is 0

### Requirement: Lean environment loading
The option `--lean-env M1,M2,...` SHALL import the given Lean modules (resolved through the Lean search path) into a Lean environment before the program is loaded, run the engine in that environment, and make available every builtin registered by `@[elpi_builtin]` in the imported modules. Without `--lean-env`, a program that calls a builtin that is only available inside a Lean environment SHALL fail at load time with an error that names the builtin and suggests `--lean-env`.

#### Scenario: Lean builtins without an environment fail clearly
- **WHEN** module `MyBuiltins` registers `@[elpi_builtin "double" "pred double i:int, o:int."]` and the command `lean-elpi p.elpi -exec main` is run on a program whose `main` calls `double`, without `--lean-env`
- **THEN** the command exits with a non-zero status and the error names `double` and mentions `--lean-env`

#### Scenario: Lean builtins work with --lean-env
- **WHEN** the same command is run as `lean-elpi p.elpi -exec main --lean-env MyBuiltins` with `MyBuiltins` on the Lean search path
- **THEN** the call to `double` succeeds, the program's output is produced and the exit status is 0

### Requirement: Interactive REPL
When `lean-elpi` is run without `-exec` or `-test`, it SHALL load the given files and start a read-eval-print loop that reads queries terminated by `.`, prints each solution as the bindings of the query variables, offers further solutions on request, prints a failure message when no (more) solutions exist, and reports load or type errors in a query without exiting. End of input SHALL terminate the REPL with exit status 0.

#### Scenario: REPL answers queries against loaded files
- **WHEN** `lean-elpi fam.elpi` is started on a file containing `parent tom bob.  parent tom liz.` and the input `parent tom X.` is entered, followed by a request for the next solution
- **THEN** the REPL prints `X = bob`, then `X = liz` on the request, then reports that no further solutions exist

### Requirement: Compiled program executables
The command `elpi_main prog` SHALL generate a Lean `main : List String → IO UInt32` definition that runs the predicate `main` of the compiled program `prog.compiled` (declared with `elpi_program`) with the command-line arguments as a list of strings, prints output through `IO`, and returns exit status 0 on success and 1 on failure. The resulting executable SHALL embed the compiled program and SHALL NOT parse or typecheck ELPI source at startup.

#### Scenario: Executable starts without parsing the program
- **WHEN** a Lake executable target consists of `elpi_program greet "main [N] :- print \"hi\" N."` followed by `elpi_main greet`, and the built executable is run with the argument `ann`
- **THEN** it prints `hi ann` and exits with status 0
- **AND** the runtime parser invocation counter remains zero for the run
