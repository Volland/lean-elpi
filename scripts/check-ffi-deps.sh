#!/usr/bin/env bash
# @tg: verifies:: [[openspec:language-bindings#Self-contained shared library#No Lean dependency at run time]]
# Fail if dist/libleanelpi depends on anything but the system's C and C++ libraries.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "$(uname -s)" = Darwin ]; then
  deps=$(otool -L dist/libleanelpi.dylib | tail -n +3 | awk '{print $1}')
else
  deps=$(ldd dist/libleanelpi.so | awk '{print $1}')
fi
echo "$deps"
if echo "$deps" | grep -i -e lean -e lake -e gmp -e libuv; then
  echo "libleanelpi still depends on a Lean library" >&2; exit 1
fi
