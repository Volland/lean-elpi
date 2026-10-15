## Why

After M3, ELPI can read and build Lean terms, but the two languages still talk about *data* in only one direction and only for simple cases. `deriving Elpi` rejects every parametric type and, as built, every recursive one, so `inductive Tree (α : Type)` cannot cross the boundary. An ELPI program cannot call an ordinary typed Lean function without hand-writing `Array Term → LazyList (Array Term)` glue. And a type that a user first designs in ELPI has to be written a second time in Lean. Coq-Elpi closes the same gap with a *shared vocabulary*: one declaration yields a Coq inductive, an Elpi `type` and the conversion code, and OCaml functions are exposed to Elpi through typed predicate declarations. This change gives LeanElpi that layer, so that the types and functions a user writes on either side are usable on the other side without glue code.

**Depends on:** `add-lean-integration` (M3), for `deriving Elpi`, the solver registry and `Elpi.query`.

## What Changes

- `deriving Elpi` accepts **type parameters** (`Tree α` gives `kind tree type -> type` and `type node tree A -> A -> tree A -> tree A`), **recursive** types and nested occurrences such as `List (Rose α)`. Indexed families are still rejected, now with a message that points to the LF extension.
- A new command `elpi_data lp%{ kind … type … }%` takes plain ELPI data declarations and defines the Lean inductive types or structures (`deriving Elpi` included), so a type may be designed on the ELPI side and used from Lean without a second definition.
- A new command `elpi_extern [partial|many] f [as "name"]` exposes a typed Lean function as an ELPI predicate. The ELPI signature is computed from the Lean type, arguments are decoded with `FromElpi` and the result is encoded with `ToElpi`. The three forms are the three determinism classes: total, semi-deterministic (`Option`) and non-deterministic (`List`).
- New builtins `lean.env.indt` and `lean.add_inductive` read a complete inductive type into ELPI and add one built by ELPI to the environment (with `casesOn`, `recOn`, `noConfusion`, `below` and `brecOn`), the counterpart of Coq-Elpi's `coq.env.indt` and `coq.env.add-indt`. Together they let ELPI write derivers that create types, not only definitions.
- A new command `#elpi_signature T` shows the ELPI declarations a derived type contributes.
- Registered builtin signatures may now refer to derived kinds and types: derived declarations are loaded before them.

## Capabilities

### New Capabilities
- `lean-interop`: parametric and recursive deriving, `elpi_data`, `elpi_extern`, `#elpi_signature`, `lean.env.indt`, `lean.add_inductive`.

### Modified Capabilities
- `lean-reflection`: the requirement "Deriving Elpi" is extended to parameters and recursion.

## Impact

**Motivating decisions:**
- [[decisions#Plain types with reflected Lean terms]]: the shared vocabulary is plain (prenex-polymorphic) ELPI types.
- [[decisions#Two-way type bridge]]: one declaration per type, generated on the other side.

**Components introduced:**
- [[components#Type interoperability]] (`Elpi/Lean/Interop.lean`)
