#!/usr/bin/env bash
# Install the conformance oracle: ELPI 1.18.x from opam, in a dedicated switch so that
# CI and developers compare against the same release. Idempotent.
# Usage: scripts/install-oracle.sh [switch-name]   (default: lean-elpi-oracle)
# @lat: [[constraints#Oracle is ELPI 1.18]]
set -euo pipefail
switch="${1:-lean-elpi-oracle}"
if ! opam switch list --short | grep -qx "$switch"; then
  opam switch create "$switch" ocaml-base-compiler.5.2.0
fi
eval "$(opam env --switch="$switch")"
opam install --yes "elpi.1.18.2"
elpi -version
echo "Run the suite with: PATH=\"\$(opam var bin --switch=$switch):\$PATH\" lake run conformance"
