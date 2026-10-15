#!/usr/bin/env bash
# @tg: implements:: [[openspec:language-bindings#Distribution#Versions agree]]
# Fail unless every binding carries the version in lakefile.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
want=$(sed -n 's/.*version := v!"\([^"]*\)".*/\1/p' lakefile.lean | head -1)
[ -n "$want" ] || { echo "no version in lakefile.lean" >&2; exit 2; }
status=0
check() { # file, extracted
  if [ "$2" != "$want" ]; then echo "version mismatch: $1 has '$2', lakefile.lean has '$want'" >&2; status=1; fi
}
check bindings/python/pyproject.toml "$(sed -n 's/^version = "\(.*\)"/\1/p' bindings/python/pyproject.toml | head -1)"
check bindings/rust/Cargo.toml "$(sed -n 's/^version = "\(.*\)"/\1/p' bindings/rust/Cargo.toml | head -1)"
check bindings/node/package.json "$(sed -n 's/.*"version": "\(.*\)".*/\1/p' bindings/node/package.json | head -1)"
for dep in $(sed -n 's/.*"@lean-elpi\/leanelpi-[a-z0-9-]*": "\(.*\)".*/\1/p' bindings/node/package.json); do
  check "bindings/node/package.json optionalDependencies" "$dep"
done
check Elpi/Ffi.lean "$(sed -n 's/^def version : String := "\(.*\)"/\1/p' Elpi/Ffi.lean)"
[ $status -eq 0 ] && echo "all versions are $want"
exit $status
