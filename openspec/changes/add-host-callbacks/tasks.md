## 1. Engine and C ABI

- [x] 1.1 `CompiledProgram.declareHost` and `hostPreds`: typechecked signature, placeholder builtin that errors without a host
- [x] 1.2 `Elpi.Ffi`: term JSON trees both ways, `hostCall` extern, `hostBuiltin`, `declare`, `solveHost`, `terms` and `fuelUsed` in answers, "out of fuel" messages
- [x] 1.3 `ffi/leanelpi.c`: `leanelpi_declare`, `leanelpi_solve_host`, `leanelpi_host_call`; header documents the term tree

## 2. Rust binding

- [x] 2.1 `Term` with serde to and from the tree, `Solution::terms`, `HostRun`, `Program::declare`, `Program::solve_host`, `Error::is_out_of_fuel`
- [x] 2.2 `bindings/rust/tests/host.rs`: recursive query over host edges, term decoding, host errors, out of fuel, no host, panics

## 3. Release

- [x] 3.1 Version 0.4.0 everywhere (`scripts/check-versions.sh`), CHANGELOG, docs
- [ ] 3.2 Tag and publish (not part of this change's implementation)
