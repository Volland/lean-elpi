# leanelpi (Python)

Run ELPI (λProlog) programs on the LeanElpi engine from Python. Needs `libleanelpi`; build it
with `scripts/build-ffi.sh` and point `LEANELPI_LIB` at it, or leave it in `dist/`.

```python
from leanelpi import Program

p = Program("pred n o:int.\nn 1.\nn 2.")
[s["X"] for s in p.solve("n X")]   # ['1', '2']
[s.terms["X"] for s in p.solve("n X")]   # [1, 2]
```

`Solution.bindings` (and `solution["X"]`) hold the values as ELPI prints them;
`Solution.terms` holds them as Python values: `int`, `float`, `str`, a `list` for an ELPI list,
`Const("anna")`, `App("pt", (1, "x"))`, `Var(name)` for an unbound variable and
`Opaque(printed)` for anything else (λ-terms).

## Host predicates (0.4)

`declare` makes a predicate whose calls Python answers during `solve_host`, so rules can ask
an LLM or a tool and still decide the conclusion themselves:

```python
from leanelpi import Program, Const, ElpiError

world = Program("""
kind person type.
type anna, marco person.
pred knows i:person, i:person.
knows anna marco.
pred same_person i:string, o:person.
pred believable i:string, i:string.
believable A B :- same_person A PA, same_person B PB, knows PA PB.
""").declare("pred same_person i:string, o:person.")

def same_person(name):                        # an LLM or a tool would go here
    return [Const(c) for c in {"Anya": ["anna"], "Marko": ["marco"]}.get(name, [])]

world.solve_host('believable "Anya" "Marko"', {"same_person": same_person})   # one solution
world.first_host('same_person "Anya" P', {"same_person": same_person}).terms   # {'P': Const('anna')}
world.solve_host('believable "Anya" "Marko"', {"same_person": lambda n: [Const("maria")]})
# ElpiError: host predicate 'same_person': unknown constant 'maria'
```

- `Program.declare(signature, name=None)` returns a new program (the old one is unchanged).
  The program may already declare the predicate, so its rules can call it, but must not have
  clauses for it. Querying it with plain `solve` raises `ElpiError`.
- `Program.solve_host(query, host, *, limit=None, fuel=None)` returns the solutions;
  `solve_host_all` returns a `HostRun(solutions, exhausted, fuel_used)` and `first_host` the
  first `Solution` or `None`.
- `host` is a dict `{name: function}`, where the function receives the `i:` arguments as
  Python values, or one function `host(name, args)` receiving every argument (unbound ones as
  `Var`). It returns an iterable of rows, one tuple of `o:` values per answer, in order (a bare
  value is a one-output row; wrap a list output as `([1, 2],)`). An empty iterable or `None`
  means the call fails; `True` means it succeeds once (a predicate with no outputs). Return
  `int`, `float`, `str`, `bool` (`tt`/`ff`), `Const`, `App` or a list.
- An exception in the host stops the run and raises `ElpiError` with the exception as
  `__cause__`; nothing unwinds through C. `KeyboardInterrupt` and `SystemExit` are re-raised.
- The engine rejects a constant the program does not know. It does not type-check host
  answers, so the binding rejects values that cannot have the declared type (a `str` for
  `o:person`, a constant declared as another kind) and turns an `int` for `o:float` into a float.
- Calls are synchronous, on the thread that called `solve_host`; a host may call the engine
  again, and several threads may run `solve_host` at once. `ElpiError.out_of_fuel` tells a
  spent `fuel=` budget from other errors.

See the [guide](https://volland.github.io/lean-elpi/book/bindings/).
