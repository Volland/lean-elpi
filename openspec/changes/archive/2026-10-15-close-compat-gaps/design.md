## Context

The upstream suite and the performance programs are ELPI's own test corpus; each rejection is a place where LeanElpi disagrees with the oracle about what a program means. This change closes the gaps that block the performance programs and those the same fixes reach.

## Decisions

### D1. Macros and multi-name binders are token rewrites

Both are pure syntax, so they are expanded on the token stream (`expandMacros`, `expandBinders` in `Parser.lean`) and the parser stays unchanged. A macro's parameters are the variables between its name and `:-`; an argument at a use is one token or one balanced group. `pi` and `sigma` are the only heads that take several names, so `f X Y\ Z` is still an application.

### D2. Undeclared constants: warn when untyped, error when typed

The oracle only warns (`constant foo has no declared type`). The specification asks for an error. A program that declares nothing is checked as the oracle checks it; the moment it declares a kind, a type or a predicate the error returns. The flag (`typed`) belongs to the program, not to the libraries it loads. The warnings are kept on the compiled program and printed by the CLI, with the hint to pass `--lean-env` when the name could be a Lean builtin.

### D3. `std.map` is an AVL tree with ELPI's types

The previous map was an unbalanced tree whose `remove` rebuilt everything. It is now height-balanced (insert and remove rebalance by one or two rotations), has the public type `std.map K V` and carries its comparison function. `std.set` is a map to `unit`. `std.int.*` fix the key type and the comparison. All of it is ELPI source in `lib/elpi/std.elpi`, written from the textbook algorithm: the standard library stays clean-room.

### D4. A bounded scan, not a different check

The unifier's first-order fast path scans a term for the variable being bound and for deeper variables. The scan stops after `scanBudget` (256) nodes and accepts the binding. Cyclic or out-of-scope bindings of terms under that size are rejected as before; a larger term is bound as ELPI binds every term.

## Risks

- A binding that creates a cycle or lets a name escape its scope through a term of more than 256 nodes is not caught.
- `std.int.set` and `std.int.map` are interpreted code where ELPI's are native, so programs that use them heavily (`set_ho`) are far slower than ELPI.
- `:index` is accepted but not used: deep or multi-argument indexing is a separate feature, and `index2` and `dt` are slow without it.
