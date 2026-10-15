#!/usr/bin/env bash
# Check that what we would publish is publishable. Needs the artefacts of scripts/package-python.sh
# and scripts/package-node.sh and a built dist/libleanelpi.*; run those first.
set -euo pipefail
cd "$(dirname "$0")/.."

# @tg: verifies:: [[openspec:language-bindings#Distribution#Versions agree]]
scripts/check-versions.sh >/dev/null
cp bindings/node/package.json /tmp/leanelpi-package.json.bak
trap 'mv /tmp/leanelpi-package.json.bak bindings/node/package.json' EXIT
sed -i.tmp 's/"version": "[^"]*"/"version": "9.9.9"/' bindings/node/package.json && rm bindings/node/package.json.tmp
if scripts/check-versions.sh >/dev/null 2>&1; then echo "check-versions.sh accepted a mismatch" >&2; exit 1; fi
mv /tmp/leanelpi-package.json.bak bindings/node/package.json
trap - EXIT
echo "ok: versions"

# @tg: verifies:: [[openspec:language-bindings#Distribution#Wheel carries the library]]
for w in dist/wheels/*.whl; do
  python3 - "$w" <<'PY'
import sys, zipfile, re
z = zipfile.ZipFile(sys.argv[1])
names = z.namelist()
assert any(re.fullmatch(r"leanelpi/libleanelpi\.(dylib|so)", n) for n in names), "library missing"
tag = [l for l in z.read([n for n in names if n.endswith("/WHEEL")][0]).decode().splitlines() if l.startswith("Tag:")]
assert tag and tag[0].startswith("Tag: py3-none-") and not tag[0].endswith("-any"), tag
print("ok: wheel", sys.argv[1].split("/")[-1], tag[0])
PY
done

# @tg: verifies:: [[openspec:language-bindings#Distribution#Packages are publishable]]
python3 -m twine check dist/wheels/*.whl
for t in dist/npm/*.tgz; do tar -tzf "$t" >/dev/null; done
(cd bindings/rust && LEANELPI_DIST="$PWD/../../dist" cargo publish --dry-run --allow-dirty 2>&1 | tail -2)
echo "ok: packages"
