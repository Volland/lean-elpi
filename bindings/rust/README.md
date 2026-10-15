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
