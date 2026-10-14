#!/usr/bin/env bash
# CI check: the import closure of Elpi/Core/*.lean must contain no Lean.Meta or Lean.Elab
# module, so the engine core stays usable from compiled executables (MetaM is not
# callable from C). Run after `lake build`.
# @lat: [[constraints#MetaM is not callable from C]]
set -euo pipefail
cd "$(dirname "$0")/.."
bad=0
for f in Elpi/Core/*.lean; do
  # direct imports of each core module
  if grep -E '^import (Lean\.(Meta|Elab)|Lean$|Lean\.Elab|Lean\.Meta)' "$f" >/dev/null; then
    echo "error: $f imports Lean.Meta/Lean.Elab" >&2
    bad=1
  fi
done
# transitive closure, as seen by the compiler
mods=$(ls Elpi/Core/*.lean | sed -e 's|/|.|g' -e 's|\.lean$||')
closure=$(lake env lean --run /dev/stdin <<'LEAN' $mods
import Lean
open Lean
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean"]
  let env ← importModules (args.toArray.map fun m => ({ module := m.toName } : Import)) {}
  for m in env.header.moduleNames do IO.println m
LEAN
)
if echo "$closure" | grep -E '^Lean\.(Meta|Elab)(\.|$)' >/dev/null; then
  echo "error: the closure of Elpi.Core.* contains:" >&2
  echo "$closure" | grep -E '^Lean\.(Meta|Elab)(\.|$)' >&2
  bad=1
fi
[ "$bad" -eq 0 ] && echo "ok: Elpi.Core.* does not depend on Lean.Meta or Lean.Elab"
exit "$bad"
