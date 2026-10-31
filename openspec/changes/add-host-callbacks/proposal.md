## Why

A host program that embeds LeanElpi (the first is tiramemsu, which keeps its facts in its own store) needs ELPI rules to read the host's data during a query, without copying every fact into the program first. It also needs answers as values, not only as the strings ELPI prints, and a way to tell a run that ran out of fuel from a broken one.

**Depends on:** `add-language-bindings`.

## What Changes

- **Host predicates.** `leanelpi_declare(program, name, sig_src, err)` declares a predicate from signature text and returns a new handle. `leanelpi_solve_host(program, query, limit, fuel, host, ctx, err)` runs a query in which every call to a declared host predicate calls `host(ctx, name, args_json)` synchronously on the calling thread. The host answers all rows of one call at once (`{"rows":[[term,...],...]}`, one term per output-mode argument) or an error (`{"error":"..."}`); `NULL` means no rows. Through plain `leanelpi_solve` a host predicate is a runtime error.
- **Structured answers.** Each solution gains `"terms"`: the bindings as JSON trees (`c`/`a` constants and applications, `i`/`f`/`s` literals, `v` unassigned variables, `o` printed for anything else). Both solve calls report `"fuelUsed"`, and running out of fuel fails with a message starting with `out of fuel`.
- **Rust binding 0.4.0.** `Term`, `Solution::terms`, `HostRun`, `Program::declare`, `Program::solve_host` with a closure, and `Error::is_out_of_fuel`. The trampoline catches panics and allocates answers with the C allocator.

## Capabilities

### Modified Capabilities
- `language-bindings`: new requirements "Host callback predicates" and "Structured answers".

## Impact

**Components changed:** [[components#C ABI]], [[components#Language bindings]], [[components#Runtime API]] (`CompiledProgram.declareHost`, `hostPreds`). Python and Node.js bindings are unchanged; they ignore the new fields.
