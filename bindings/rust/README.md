# leanelpi (Rust)

Rust bindings for [LeanElpi](https://volland.github.io/lean-elpi/), the ELPI dialect of
λProlog implemented in Lean 4. Load a program once, add clauses, and query it many times.

```rust
use leanelpi::Program;

let p = Program::new("pred n o:int.\nn 1.\nn 2.")?;
for s in p.solve("n X")? {
    println!("{}", s.bindings["X"]);
}
# Ok::<(), leanelpi::Error>(())
```

Every solution also carries its bindings as terms (`s.terms["X"]`, a [`Term`]), and a program
can declare **host predicates** that a closure answers during the query:

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
assert_eq!(run.solutions.len(), 2);            // X = b, X = c
# Ok::<(), leanelpi::Error>(())
```

The closure gets the predicate name and one term per argument (unbound ones as `Term::Var`)
and returns one row per answer, a term for each output-mode argument; `Ok(vec![])` is
failure and `Err` a runtime error. It runs synchronously on the calling thread; a panic in it
becomes an error. `HostRun` also reports `exhausted` and `fuel_used`; a run that exceeds its
fuel fails with an error for which `is_out_of_fuel()` holds.

## Setup

The crate links the native library `libleanelpi`, which is too large for crates.io. Get it
first (from the [GitHub release](https://github.com/Volland/lean-elpi/releases) for your
platform, or build it with `scripts/build-ffi.sh`), then point the build at its directory:

```bash
export LEANELPI_DIST=/path/to/dir/containing/libleanelpi
cargo add leanelpi
cargo run
```

The build script adds an rpath, so `cargo run` and `cargo test` find the library. To ship a
binary, put `libleanelpi` beside it and link with `-C link-arg=-Wl,-rpath,$ORIGIN` (Linux) or
`@executable_path` (macOS).

Full guide: <https://volland.github.io/lean-elpi/book/bindings/>.
