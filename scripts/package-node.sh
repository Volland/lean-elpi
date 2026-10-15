#!/usr/bin/env bash
# Build the npm tarballs in dist/npm: lean-elpi-leanelpi-VERSION.tgz (the loader) and
# lean-elpi-leanelpi-PLATFORM-ARCH-VERSION.tgz (the native library for this machine).
set -euo pipefail
cd "$(dirname "$0")/.."
[ -f dist/libleanelpi.dylib ] || [ -f dist/libleanelpi.so ] || scripts/build-ffi.sh
VERSION=$(node -p "require('./bindings/node/package.json').version")
OS=$(node -p "process.platform"); CPU=$(node -p "process.arch")
NAME="leanelpi-$OS-$CPU"
PKG="@lean-elpi/$NAME"
OUT=dist/npm; rm -rf "$OUT/$NAME"; mkdir -p "$OUT/$NAME"
cp dist/libleanelpi.* LICENSE "$OUT/$NAME/"
cat > "$OUT/$NAME/package.json" <<JSON
{
  "name": "$PKG",
  "version": "$VERSION",
  "description": "The native LeanElpi library for $OS-$CPU, loaded by the leanelpi package",
  "os": ["$OS"],
  "cpu": ["$CPU"],
  "files": ["libleanelpi.*", "LICENSE"],
  "publishConfig": { "access": "public" },
  "license": "Apache-2.0",
  "repository": { "type": "git", "url": "git+https://github.com/Volland/lean-elpi.git" }
}
JSON
(cd "$OUT/$NAME" && npm pack --pack-destination ..)
(cd bindings/node && npm pack --pack-destination ../../$OUT)
ls -la "$OUT"/*.tgz
