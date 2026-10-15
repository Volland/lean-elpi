#!/usr/bin/env bash
# @tg: implements:: [[openspec:language-bindings#Self-contained shared library]]
# Build dist/libleanelpi.{dylib,so}: the Elpi engine, the Lean runtime and the C API of
# ffi/leanelpi.h in ONE self-contained shared library. Only the Lean toolchain (elan) and a C
# compiler are needed to build it; nothing but the system C libraries is needed to run it.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Elpi:static ElpiFfi:static
PREFIX="$(lean --print-prefix)"
LIBS=".lake/build/lib"
OUT=dist
mkdir -p "$OUT"

# The shim needs the system libc headers, which leanc's bundled sysroot lacks.
"${CC:-cc}" -c -fPIC -O2 -I"$PREFIX/include" -o "$OUT/leanelpi.o" ffi/leanelpi.c

OURS=("$LIBS/liblean_x2delpi_Elpi.a" "$LIBS/liblean_x2delpi_ElpiFfi.a")
RUNTIME=(-L"$PREFIX/lib/lean" -L"$PREFIX/lib" -lLean -lStd -lInit -lleancpp -lleanrt -lgmp -luv)

case "$(uname -s)" in
  Darwin)
    EXT=dylib
    "$PREFIX/bin/leanc" -shared -fPIC -Wl,-install_name,@rpath/libleanelpi.dylib \
      -o "$OUT/libleanelpi.$EXT" "$OUT/leanelpi.o" \
      -Wl,-force_load,"${OURS[0]}" -Wl,-force_load,"${OURS[1]}" \
      "${RUNTIME[@]}" -Wl,-dead_strip -Wl,-dead_strip_dylibs
    strip -x "$OUT/libleanelpi.$EXT"
    # The toolchain's objects carry a placeholder minimum OS (99.0); declare the real one.
    vtool -set-build-version macos 11.0 11.0 -replace -output "$OUT/libleanelpi.tmp" "$OUT/libleanelpi.$EXT"
    mv "$OUT/libleanelpi.tmp" "$OUT/libleanelpi.$EXT"
    codesign -s - -f "$OUT/libleanelpi.$EXT" 2>/dev/null
    ;;
  *)
    EXT=so
    "$PREFIX/bin/leanc" -shared -fPIC -Wl,-soname,libleanelpi.so \
      -o "$OUT/libleanelpi.$EXT" "$OUT/leanelpi.o" \
      -Wl,--whole-archive "${OURS[@]}" -Wl,--no-whole-archive \
      "${RUNTIME[@]}" -Wl,--gc-sections -Wl,--as-needed -Wl,-Bsymbolic
    strip --strip-unneeded "$OUT/libleanelpi.$EXT"
    ;;
esac

rm "$OUT/leanelpi.o"
cp ffi/leanelpi.h "$OUT/"
echo "built $OUT/libleanelpi.$EXT ($(du -h "$OUT/libleanelpi.$EXT" | cut -f1))"
