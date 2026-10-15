# leanelpi (Python)

Run ELPI (λProlog) programs on the LeanElpi engine from Python. Needs `libleanelpi`; build it
with `scripts/build-ffi.sh` and point `LEANELPI_LIB` at it, or leave it in `dist/`.

```python
from leanelpi import Program

p = Program("pred n o:int.\nn 1.\nn 2.")
[s["X"] for s in p.solve("n X")]   # ['1', '2']
```

See the [guide](https://volland.github.io/lean-elpi/book/bindings/).
