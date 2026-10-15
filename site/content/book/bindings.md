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
 Python        ctypes        7 functions, handles          + Lean runtime,
 Node.js       koffi         and strings                   in one file
 Rust          extern "C"
```

Only integers and strings cross the boundary. A program lives inside the Lean runtime and your code holds a numeric *handle* to it. Loading, asserting a clause and running a query are calls on that handle. A query returns JSON text with one object per solution: the query variables with their values as ELPI prints them, and any constraints still suspended.

```json
{"solutions":[{"bindings":{"R":"[1, 2, 3]"},"constraints":[]}],"exhausted":true}
```

`exhausted` is `false` when a limit you set stopped the search before the last solution.

Programs are immutable. Adding a clause gives you a new handle and leaves the old program as it was, which is the same persistence the Lean library offers. The handle table is safe to use from several threads.

The native library is a single file. The engine and the Lean runtime are linked together, so a machine needs no Lean installation, only the C and C++ libraries every system has. That is why a wheel is about 44 MB. Starting the runtime takes about a second the first time you load a program in a process.

### What you get, and what you do not

You get the engine, the standard library, typed clauses, modes, constraints and CHR. You do not get the Lean-facing builtins (`lean.*`, `{{ … }}`, `elpi_extern`): they need a Lean environment and stay in the Lean host. Values come back as strings, so decode them in your own code.

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

To ship a Rust binary, put `libleanelpi` next to it and link with `-C link-arg=-Wl,-rpath,@executable_path` on macOS or `-Wl,-rpath,$ORIGIN` on Linux (for example from your own `build.rs`).

## Other languages

Any language with a C FFI can follow the same steps. `dist/leanelpi.h` documents the functions: call `leanelpi_init` once, then `leanelpi_load` for a handle, `leanelpi_solve` for JSON, and release every returned string with `leanelpi_free_string`. Errors come back through the `err` out-parameter.

## When a subprocess is enough

If you only run a file and read the output, call the `lean-elpi` executable (see *Using it standalone*) and skip the library. The library is the better choice when you call the engine often, keep a program in memory, or add clauses between queries.

## Publishing your own build

The release procedure, account setup for PyPI, npm and crates.io, and the CI workflow are described in `PUBLISHING.md` in the repository.
