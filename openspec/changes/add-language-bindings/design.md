## Context

The runtime library is pure Lean. Calling it from C means initialising the Lean runtime and handling `lean_object*` reference counts, which every binding author would get wrong. Distribution is harder than calling: the Lean runtime is 177 MB as a shared library.

## Decisions

- **Handles and strings.** Programs live in a table inside the Lean runtime (`IO.Ref (Array (Option CompiledProgram))`) and are named by a `uint64`. All other values are UTF-8 strings. Solutions are returned as JSON so each binding needs only a JSON parser. The table is updated with `modifyGet`, so concurrent loads never share a handle (an earlier version read and wrote separately and handed two threads the same slot).
- **One self-contained library on macOS.** `build-ffi.sh` links the engine, `libLean`, `libStd`, `libInit`, `libleancpp`, `libleanrt`, GMP and libuv into one shared library that depends only on the system C and C++ libraries. A user installs one file; it is about 45 MB compressed.
- **Node through `koffi`.** `koffi` loads a C library at run time with prebuilt binaries, so installing the package needs no compiler or `node-gyp`.
- **Python through `ctypes`.** No compiled extension, so one wheel per platform serves every Python 3 version (`py3-none-<platform>`).
- **Native code per platform package.** For Node the native library ships in `@lean-elpi/leanelpi-<os>-<cpu>` packages selected by `os` and `cpu` in `optionalDependencies`, so an install downloads one library, not all of them.
- **Rust links a library it does not build.** crates.io caps a crate at 10 MB, so the crate cannot carry the library. Its build script finds `libleanelpi` through `LEANELPI_DIST` and fails with instructions otherwise.
- **One version.** `lakefile.lean` is the source of truth; `scripts/check-versions.sh` fails when a binding disagrees.

## Risks

- Only macOS on Apple silicon is built and tested locally; Linux and Intel macOS builds run in CI at release time.
- Starting the runtime takes about a second because every `Lean` module initialises.
