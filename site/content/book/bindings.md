---
title: From Python, Node.js and Rust
order: 12
summary: Load ELPI programs and run queries from Python, Node.js or Rust through one native library. How it works, how to install it, how to use it.
---
# From Python, Node.js and Rust

LeanElpi is written in Lean, but programs written in other languages can load an ELPI program once, add clauses to it and query it many times. Three bindings do this: `pip install leanelpi`, `npm install @lean-elpi/leanelpi` and the `leanelpi` crate. All three sit on one native library.

## How it works

```
 your code ──► binding ──► libleanelpi (C interface) ──► ELPI engine in Lean
 Python        ctypes        9 functions, handles          + Lean runtime,
 Node.js       koffi         and strings                   in one file
 Rust          extern "C"
```

Only integers and strings cross the boundary. A program lives inside the Lean runtime and your code holds a numeric *handle* to it. Loading, asserting a clause and running a query are calls on that handle. A query returns JSON text with one object per solution: the query variables with their values as ELPI prints them, and any constraints still suspended.

```json
{"solutions":[{"bindings":{"R":"[1, 2, 3]"},
               "terms":{"R":{"c":"::","a":[{"i":1},{"c":"::","a":[{"i":2},{"c":"::","a":[{"i":3},{"c":"[]"}]}]}]}},
               "constraints":[]}],
 "exhausted":true,"fuelUsed":3}
```

`terms` holds the same values as trees: `{"c":name}` a constant, `{"c":name,"a":[...]}` a constant applied, `{"i":..}`, `{"f":..}` and `{"s":..}` literals, `{"v":name}` an unassigned variable and `{"o":printed}` anything else, such as a λ-term.

`exhausted` is `false` when a limit you set stopped the search before the last solution.

Programs are immutable. Adding a clause gives you a new handle and leaves the old program as it was, which is the same persistence the Lean library offers. The handle table is safe to use from several threads.

A machine needs no Lean installation. On macOS the native library is a single file with the engine and the Lean runtime linked together. On Linux the toolchain's runtime cannot be linked into a shared object, so `libleanelpi.so` comes with `libleanshared.so` beside it and finds it through an `$ORIGIN` rpath; the wheels and npm packages carry both. A wheel is about 44 MB. Starting the runtime takes about a second the first time you load a program in a process.

### What you get, and what you do not

You get the engine, the standard library, typed clauses, modes, constraints and CHR. You do not get the Lean-facing builtins (`lean.*`, `{{ … }}`, `elpi_extern`): they need a Lean environment and stay in the Lean host. Values come back as strings and, since 0.4, as JSON term trees; host predicates are answered by a C callback, which only the Rust binding wraps so far.

## Install

| Language | Command | Notes |
|---|---|---|
| Python ≥ 3.9 | `pip install leanelpi` | a platform wheel with the library inside (on Linux, with the Lean runtime library beside it) |
| Node.js ≥ 18 | `npm install @lean-elpi/leanelpi` | npm picks the library for your platform; no compiler needed |
| Rust ≥ 1.70 | `cargo add leanelpi` | needs the library separately, see below |

Supported platforms: macOS (Apple silicon and Intel) and Linux (x86-64 and arm64). Windows is not supported yet.

To build the library yourself, you need the Lean toolchain (through `elan`) and a C compiler:

```bash
git clone https://github.com/Volland/lean-elpi && cd lean-elpi
scripts/build-ffi.sh          # writes dist/libleanelpi.dylib or .so, and dist/leanelpi.h
```

## Python

```python
from leanelpi import Program

p = Program("""
pred app i:list int, i:list int, o:list int.
app [] L L.
app [X|Xs] L [X|R] :- app Xs L R.
""")

p.first("app [1,2] [3] R")            # {'R': '[1, 2, 3]'}
p.ask("app [1] [2] [1,2]")            # True
for s in p.solve("app X Y [1,2]"):    # every split of [1,2]
    print(s["X"], s["Y"])

p2 = p.assert_clause("app [] [] [].")  # a new program; p is unchanged
sols, done = p.solve_all("app X Y [1,2]", limit=2)   # done is False: the limit cut it short
```

Failure is an empty result, not an exception. Parse errors, type errors and running out of fuel raise `leanelpi.ElpiError`. A `Program` frees its handle when it is garbage collected, or earlier with `close()` or a `with` block. Pass `fuel=` to bound the number of resolution steps.

## Node.js

```js
const { Program, ElpiError } = require('@lean-elpi/leanelpi');

const p = new Program(`
pred app i:list int, i:list int, o:list int.
app [] L L.
app [X|Xs] L [X|R] :- app Xs L R.
`);

p.first('app [1,2] [3] R');                  // { R: '[1, 2, 3]' }
p.ask('app [1] [2] [1,2]');                  // true
for (const s of p.solve('app X Y [1,2]')) console.log(s.bindings.X, s.bindings.Y);

const p2 = p.assertClause('app [] [] [].');  // a new program; p is unchanged
const { solutions, exhausted } = p.solveAll('app X Y [1,2]', { limit: 2 });

try { new Program('pred q o:int.\nq foo bar.'); }
catch (e) { if (e instanceof ElpiError) console.error(e.message); }
```

TypeScript declarations ship with the package. Calls are synchronous: a long search blocks the event loop, so run heavy queries in a worker thread and bound them with `fuel`. `close()` frees a program early; otherwise it is freed when garbage collected.

## Rust

Add the crate and point its build script at the native library:

```bash
export LEANELPI_DIST=/path/to/directory/with/libleanelpi    # from the GitHub release, or dist/
cargo add leanelpi
```

The crate is small because crates.io limits crates to 10 MB; the library is not inside it. Download `libleanelpi-<platform>.tar.gz` from the [GitHub release](https://github.com/Volland/lean-elpi/releases) and unpack it, or build it as above. The build script links the library and adds an rpath, so `cargo run` and `cargo test` find it.

```rust
use leanelpi::Program;

fn main() -> Result<(), leanelpi::Error> {
    let p = Program::new(
        "pred app i:list int, i:list int, o:list int.\n\
         app [] L L.\n\
         app [X|Xs] L [X|R] :- app Xs L R.",
    )?;

    let s = p.first("app [1,2] [3] R")?.expect("a solution");
    assert_eq!(s.bindings["R"], "[1, 2, 3]");

    for s in p.solve("app X Y [1,2]")? {
        println!("{} {}", s.bindings["X"], s.bindings["Y"]);
    }

    let p2 = p.assert_clause("app [] [] [].")?;    // p is unchanged
    let (some, exhausted) = p2.solve_with("app X Y [1,2]", Some(2), None)?;
    println!("{} solutions, exhausted: {exhausted}", some.len());
    Ok(())
}
```

`Program` is `Send` and `Sync`, so an `Arc<Program>` can serve queries from many threads at once. Dropping a `Program` frees its handle.

### Host predicates

A Rust program can answer predicates itself while a query runs, for example to let ELPI rules read facts that live in the program's own store. Declare the predicate on a program, then pass a closure to `solve_host`:

```rust
use leanelpi::{Program, Term};

let p = Program::new(
    "kind node type.\ntype a, b, c node.\n\
     pred edge i:node, o:node.\npred path i:node, o:node.\n\
     path X Y :- edge X Y.\npath X Z :- edge X Y, path Y Z.",
)?
.declare("edge", "pred edge i:node, o:node.")?;
let edges = [("a", "b"), ("b", "c")];
let run = p.solve_host("path a X", 0, 0, |_name, args| {
    let Term::Const(from) = &args[0] else { return Err("unbound source".into()) };
    Ok(edges.iter().filter(|e| e.0 == from).map(|e| vec![Term::Const(e.1.into())]).collect())
})?;
for s in &run.solutions {
    println!("{:?}", s.terms["X"]);                 // Const("b"), Const("c")
}
```

The closure receives the predicate's name and its arguments as `Term`s (unbound ones as `Term::Var`) and returns one row per answer, holding a term for each output-mode argument in order. An empty list is failure; `Err(message)` stops the run with an error, and so does a panic. Rows may contain constants the program knows, applications of them and literals. The closure runs on the calling thread, inside `solve_host`; all rows of one call are collected before the search goes on. A query that reaches a host predicate through plain `solve` is an error. When fuel runs out, the error's `is_out_of_fuel()` is true; a finished run reports `fuel_used`.

In C the same pair is `leanelpi_declare` and `leanelpi_solve_host` with a `leanelpi_host_fn` callback, which returns a `malloc`'d JSON string, `{"rows":[[term,...],...]}` or `{"error":"..."}`, that the library frees.

To ship a Rust binary, put `libleanelpi` (and, on Linux, the `libleanshared` files from the same archive) next to it and link with `-C link-arg=-Wl,-rpath,@executable_path` on macOS or `-Wl,-rpath,$ORIGIN` on Linux (for example from your own `build.rs`).

## Other languages

Any language with a C FFI can follow the same steps. `dist/leanelpi.h` documents the functions: call `leanelpi_init` once, then `leanelpi_load` for a handle, `leanelpi_solve` for JSON, and release every returned string with `leanelpi_free_string`. Errors come back through the `err` out-parameter.

## When a subprocess is enough

If you only run a file and read the output, call the `lean-elpi` executable (see *Using it standalone*) and skip the library. The library is the better choice when you call the engine often, keep a program in memory, or add clauses between queries.

## Publishing your own build

The release procedure, account setup for PyPI, npm and crates.io, and the CI workflow are described in `PUBLISHING.md` in the repository.
