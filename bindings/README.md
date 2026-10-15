# Bindings

Python, Node.js and Rust bindings over one C library, `libleanelpi`, built from
`Elpi/Ffi.lean` and `ffi/leanelpi.c`. The user guide is the book chapter
[From Python, Node.js and Rust](https://volland.github.io/lean-elpi/book/bindings/)
(`site/content/book/bindings.md`); how to release them is in [`PUBLISHING.md`](../PUBLISHING.md).

```bash
scripts/build-ffi.sh                          # dist/libleanelpi.{dylib,so} and dist/leanelpi.h
(cd bindings/python && python -m pytest)      # needs pytest
(cd bindings/node && npm install && npm test)
(cd bindings/rust && cargo test)
```

| Directory | Package | How it reaches the library |
|---|---|---|
| `python/` | `leanelpi` on PyPI | `ctypes`; the wheel contains the library |
| `node/` | `@lean-elpi/leanelpi` on npm | `koffi`; the library comes from `@lean-elpi/leanelpi-<os>-<cpu>` |
| `rust/` | `leanelpi` on crates.io | links `libleanelpi` found through `LEANELPI_DIST` |

The requirements and scenarios are in `openspec/changes/add-language-bindings/`; each test
carries an `@tg: verifies::` comment naming its scenario.
