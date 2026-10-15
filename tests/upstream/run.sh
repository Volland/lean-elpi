#!/usr/bin/env bash
# Upstream compatibility suite: run the ELPI 1.18 project's own test programs
# (copied under sources/, registry in manifest.tsv) on lean-elpi and judge each
# one by the upstream rule: exit status 0 is success, anything else is failure,
# unless the registry expects failure or an output pattern.
#
# Usage: tests/upstream/run.sh [lean|oracle] [name-regex]
#   lean    run lean-elpi (default)
#   oracle  run the real ELPI instead; proves the harness and the copy are sound
#
# Environment: ELPI_ORACLE (default elpi), LEAN_ELPI (default lake build output),
# UPSTREAM_TIMEOUT seconds per test (20), UPSTREAM_PERF=1 to include the
# performance categories, UPSTREAM_SOURCES to use another tests/sources tree
# (e.g. the full upstream one, so big skipped tests run),
# UPSTREAM_KNOWN register file (default known-failures.md next to this script).
# @lat: [[components#Upstream compatibility suite]]
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
engine="${1:-lean}"
filter="${2:-.}"
out="$here/out"
sources="${UPSTREAM_SOURCES:-$here/sources}"
limit="${UPSTREAM_TIMEOUT:-20}"
known="${UPSTREAM_KNOWN:-$here/known-failures.md}"
case "$engine" in
  lean)   exe="${LEAN_ELPI:-$root/.lake/build/bin/lean-elpi}" ;;
  oracle) exe="${ELPI_ORACLE:-elpi}" ;;
  *) echo "usage: run.sh [lean|oracle] [name-regex]" >&2; exit 2 ;;
esac
if ! command -v "$exe" >/dev/null 2>&1 && [ ! -x "$exe" ]; then
  echo "error: engine '$exe' not found${engine:+ (for lean: run lake build)}" >&2; exit 2
fi
mkdir -p "$out"

is_known() { grep -q -E "^## $1\$" "$known" 2>/dev/null; }

# Does the combined output satisfy the expected pattern of test $1?
output_matches() {
  local name="$1" kind="$2" want
  want="$(<"$here/expected/$name.out")"
  if [ "$kind" = fixed ]; then
    [[ "$(<"$3")" == *"$want"* ]]
  else
    grep -q -E -e "$want" "$3"
  fi
}

passed=0; failed=0; known_n=0; skipped=0; stale=0
while IFS='|' read -r name cat source expect kind flags input skip; do
  case "$name" in '#'*|'') continue ;; esac
  [[ "$name" =~ $filter ]] || continue
  case "$cat" in performance*) [ "${UPSTREAM_PERF:-0}" = 1 ] || { skipped=$((skipped+1)); continue; } ;; esac
  if [ -n "$skip" ] || [ ! -e "$sources/$source" ]; then
    echo "skip   $name (${skip:-source missing})"; skipped=$((skipped+1)); continue
  fi
  if [[ "$flags" == *-legacy-parser* ]] && ! "$exe" -legacy-parser-available >/dev/null 2>&1; then
    echo "skip   $name (engine has no legacy parser)"; skipped=$((skipped+1)); continue
  fi
  log="$out/$name.$engine.log"
  args=(-test -I . ${flags//,/ } "$source")
  stdin=/dev/null; [ -n "$input" ] && stdin="$sources/$input"
  ( cd "$sources" && perl -e 'alarm shift; exec @ARGV' "$limit" "$exe" "${args[@]}" <"$stdin" >"$log" 2>&1 )
  rc=$?
  ok=no
  if [ $rc -eq 0 ]; then
    case "$expect" in
      success) ok=yes ;;
      output) output_matches "$name" "$kind" "$log" && ok=yes ;;
    esac
  elif [ $rc -ne 142 ]; then   # 142 = killed by the timeout alarm
    case "$expect" in
      failure) ok=yes ;;
      failure-output) output_matches "$name" "$kind" "$log" && ok=yes ;;
    esac
  fi
  if [ $ok = yes ]; then
    if is_known "$name"; then echo "stale  $name (passes; remove it from known-failures.md)"; stale=$((stale+1))
    else echo "pass   $name"; fi
    passed=$((passed+1))
  elif is_known "$name"; then
    echo "known  $name (registered, exit $rc)"; known_n=$((known_n+1))
  else
    echo "FAIL   $name (exit $rc, expected $expect) — see ${log#"$root/"}"; failed=$((failed+1))
  fi
done <"$here/manifest.tsv"
echo "summary [$engine]: $passed passed, $known_n known failures, $failed failed, $skipped skipped"
[ "$failed" -eq 0 ]
