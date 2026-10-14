#!/usr/bin/env bash
# Conformance harness: run every corpus program (its nullary `main`, via -test)
# under the ELPI 1.18 oracle and under lean-elpi, then compare standard output
# and exit status. Standard error (timings, warnings) is kept but not compared.
#
# Usage: tests/conformance/run.sh [record|compare]
#   record   store the oracle output of each program as corpus/<name>.expected
#   compare  run both engines and diff them (default)
#
# Environment: ELPI_ORACLE (default: elpi), LEAN_ELPI (default: the lake build
# output), CONFORMANCE_TIMEOUT seconds per program (default: 20),
# CONFORMANCE_DIVERGENCES register file (default: divergences.md next to this script).
# @lat: [[components#Conformance harness]]
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
mode="${1:-compare}"
out="$here/out"
oracle="${ELPI_ORACLE:-elpi}"
lean_elpi="${LEAN_ELPI:-$root/.lake/build/bin/lean-elpi}"
limit="${CONFORMANCE_TIMEOUT:-20}"
divergences="${CONFORMANCE_DIVERGENCES:-$here/divergences.md}"
mkdir -p "$out"

# @tg: implements:: [[openspec:elpi-conformance#Oracle version pinning]]
check_oracle_version() {
  local want="1.18" have
  if ! command -v "$oracle" >/dev/null 2>&1; then
    echo "error: oracle '$oracle' not found; ELPI $want.x is required" >&2
    exit 2
  fi
  have="$("$oracle" -version 2>/dev/null | head -n1 || true)"
  case "$have" in
    "$want".*) ;;
    *) echo "error: ELPI $want.x is required as oracle, found '${have:-unknown}'" >&2
       exit 2 ;;
  esac
}

# Run one engine on one program with a timeout; writes <name>.<tag>{,.err,.status}.
run_engine() {
  local tag="$1" prog="$2" name status
  shift 2
  name="$(basename "$prog" .elpi)"
  set +e
  perl -e 'alarm shift; exec @ARGV' "$limit" "$@" -test "$prog" \
    >"$out/$name.$tag" 2>"$out/$name.$tag.err"
  status=$?
  set -e
  echo "$status" >"$out/$name.$tag.status"
}

# Timing lines are the only normalisation so far; fresh-variable and
# eigenvariable renaming is still to do (see the requirement text).
normalise() {
  grep -v -E '^(Parsing|Compilation|Typechecking|Execution) time:' "$1" || true
}

# @tg: implements:: [[openspec:elpi-conformance#Known divergence register]]
is_registered_divergence() {
  grep -q -E "^## $1(\\.elpi)?\$" "$divergences"
}

# @tg: implements:: [[openspec:elpi-conformance#Differential answer comparison]] {confidence: partial}
compare_outputs() {
  local name="$1"
  if diff -u <(normalise "$out/$name.oracle") <(normalise "$out/$name.lean") >"$out/$name.diff" \
     && cmp -s "$out/$name.oracle.status" "$out/$name.lean.status"; then
    return 0
  fi
  {
    echo "exit status: oracle $(cat "$out/$name.oracle.status"), lean-elpi $(cat "$out/$name.lean.status")"
  } >>"$out/$name.diff"
  return 1
}

# @tg: implements:: [[openspec:elpi-conformance#Shared conformance corpus]] {confidence: partial}
run_corpus() {
  local failed=0 passed=0 known=0 prog name
  for prog in "$here"/corpus/*.elpi; do
    name="$(basename "$prog" .elpi)"
    run_engine oracle "$prog" "$oracle"
    if [ "$mode" = record ]; then
      normalise "$out/$name.oracle" >"$here/corpus/$name.expected"
      echo "rec    $name"
      continue
    fi
    run_engine lean "$prog" "$lean_elpi"
    if compare_outputs "$name"; then
      if is_registered_divergence "$name"; then
        echo "stale  $name (matches the oracle; remove it from divergences.md)"
      else
        echo "pass   $name"
      fi
      passed=$((passed + 1))
    elif is_registered_divergence "$name"; then
      echo "known  $name (registered divergence)"
      known=$((known + 1))
    else
      echo "FAIL   $name"
      cat "$out/$name.diff"
      failed=$((failed + 1))
    fi
  done
  [ "$mode" = record ] && return 0
  echo "summary: $passed passed, $known known divergences, $failed failed"
  [ "$failed" -eq 0 ]
}

check_oracle_version
if [ "$mode" != record ] && [ ! -x "$lean_elpi" ]; then
  echo "error: $lean_elpi not built (run lake build)" >&2
  exit 2
fi
run_corpus
