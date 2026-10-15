## Why

LeanElpi runs only inside Lean or as the `lean-elpi` executable. Programs written in Python, Node.js or Rust can reach the engine only by starting a process per query, which loses the loaded program and costs a Lean start-up each time. A small C interface over the runtime library lets any of them load a program once, extend it and query it many times. The libraries must install with the ordinary package managers (`pip`, `npm`, `cargo`) on a machine that has no Lean toolchain.

**Depends on:** `add-elpi-core` (M1), for the runtime library API.

## What Changes

- A C ABI (`Elpi/Ffi.lean`, `ffi/leanelpi.{h,c}`) with opaque program handles; answers are JSON text.
- One self-contained shared library, `libleanelpi`, built by `scripts/build-ffi.sh`, with the Lean runtime linked in.
- Language bindings: Python (`ctypes`), Node.js (`koffi`, with TypeScript types) and Rust (safe wrapper crate).
- Packaging and release: platform wheels, per-platform npm packages with a loader package, a crate, and a release workflow that publishes all three from a version tag.
- Documentation: a book chapter, README sections, a publishing guide.

## Capabilities

### New Capabilities
- `language-bindings`: the C ABI, the shared library, the three bindings and their distribution.

## Impact

**Motivating decisions:**
- [[decisions#Handle-and-string C ABI]]: no Lean object crosses the boundary.

**Components introduced:**
- [[components#C ABI]] (`Elpi/Ffi.lean`, `ffi/`)
- [[components#Language bindings]] (`bindings/`)
