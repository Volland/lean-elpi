#!/usr/bin/env bash
# @tg: implements:: [[openspec:language-bindings#Distribution#Wheel carries the library]]
# Build the platform wheel dist/wheels/leanelpi-VERSION-py3-none-PLATFORM.whl.
# Needs `python -m pip install build twine`. Set LEANELPI_WHEEL_PLAT to override the tag
# (Linux releases use a manylinux tag).
set -euo pipefail
cd "$(dirname "$0")/.."
[ -f dist/libleanelpi.dylib ] || [ -f dist/libleanelpi.so ] || scripts/build-ffi.sh
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  : "${LEANELPI_WHEEL_PLAT:=macosx_11_0_arm64}" ;;
  Darwin-x86_64) : "${LEANELPI_WHEEL_PLAT:=macosx_11_0_x86_64}" ;;
  Linux-x86_64)  : "${LEANELPI_WHEEL_PLAT:=manylinux_2_28_x86_64}" ;;
  Linux-aarch64) : "${LEANELPI_WHEEL_PLAT:=manylinux_2_28_aarch64}" ;;
  *) echo "unsupported platform" >&2; exit 1 ;;
esac
export LEANELPI_WHEEL_PLAT
rm -f bindings/python/leanelpi/lib*
cp dist/lib*.dylib dist/lib*.so* bindings/python/leanelpi/ 2>/dev/null || true
rm -rf bindings/python/build bindings/python/*.egg-info
python -m build --wheel --outdir dist/wheels bindings/python
rm -f bindings/python/leanelpi/lib*
python -m twine check dist/wheels/*.whl
