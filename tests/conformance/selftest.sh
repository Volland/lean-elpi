#!/usr/bin/env bash
# Self-test of the conformance harness. It drives run.sh with stand-in engines:
# the oracle itself (must match), an engine that reverses output lines (must
# diverge) and a fake oracle reporting another version (must be refused).
# Needs the ELPI 1.18 oracle on PATH. Usage: tests/conformance/selftest.sh
# @lat: [[components#Conformance harness]]
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
run="$here/run.sh"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
oracle="$(command -v elpi)"
failures=0

# reverse the lines with awk: `tail -r` is BSD-only and GNU tail has no such option
printf '#!/bin/sh\nelpi "$@" >"%s/rev.out" 2>/dev/null; awk '"'"'{l[NR]=$0} END{for(i=NR;i>0;i--)print l[i]}'"'"' "%s/rev.out"\n' "$tmp" "$tmp" >"$tmp/reversing"
printf '#!/bin/sh\necho 2.0.0\n' >"$tmp/elpi2"
chmod +x "$tmp/reversing" "$tmp/elpi2"
: >"$tmp/no-divergences.md"
printf '# Known divergences\n\n## append\n\nTest entry: output order differs.\n' >"$tmp/append-divergence.md"

check() {
  local label="$1" ok="$2"
  if [ "$ok" = yes ]; then echo "ok    $label"; else echo "FAIL  $label"; failures=$((failures + 1)); fi
}

# @tg: verifies:: [[openspec:elpi-conformance#Shared conformance corpus#Every corpus program runs on both engines]]
test_every_program_runs_on_both_engines() {
  local log n programs ok=yes
  log="$(LEAN_ELPI="$oracle" CONFORMANCE_DIVERGENCES="$tmp/no-divergences.md" "$run" 2>&1)"
  programs="$(ls "$here"/corpus/*.elpi "$here"/corpus/*/*.elpi 2>/dev/null | grep -v '/lib/' | wc -l | tr -d ' ')"
  for p in "$here"/corpus/*.elpi "$here"/corpus/*/*.elpi; do
    [ -f "$p" ] || continue
    case "$p" in */lib/*) continue ;; esac
    n="${p#"$here"/corpus/}"; n="${n%.elpi}"; n="${n//\//-}"
    [ -f "$here/out/$n.oracle.status" ] && [ -f "$here/out/$n.lean.status" ] || ok=no
  done
  [ "$(echo "$log" | grep -c -E '^(pass|FAIL|known|stale) ')" = "$programs" ] || ok=no
  check "every corpus program runs on both engines" "$ok"
}

# @tg: verifies:: [[openspec:elpi-conformance#Differential answer comparison#Matching answers pass]]
test_matching_answers_pass() {
  local log status ok=yes
  log="$(LEAN_ELPI="$oracle" CONFORMANCE_DIVERGENCES="$tmp/no-divergences.md" "$run" 2>&1)"; status=$?
  [ "$status" -eq 0 ] || ok=no
  grep -q '^pass   append$' <<<"$log" || ok=no
  check "matching answers pass" "$ok"
}

# @tg: verifies:: [[openspec:elpi-conformance#Differential answer comparison#Divergent answers fail with a diff]]
test_divergent_answers_fail_with_a_diff() {
  local log status ok=yes
  log="$(LEAN_ELPI="$tmp/reversing" CONFORMANCE_DIVERGENCES="$tmp/no-divergences.md" "$run" 2>&1)"; status=$?
  [ "$status" -ne 0 ] || ok=no
  grep -q '^FAIL   append$' <<<"$log" || ok=no
  grep -q '^@@ ' <<<"$log" || ok=no
  grep -q '^exit status: oracle 0, lean-elpi 0$' <<<"$log" || ok=no
  check "divergent answers fail with a diff" "$ok"
}

# @tg: verifies:: [[openspec:elpi-conformance#Oracle version pinning#Unexpected oracle version is reported]]
test_unexpected_oracle_version_is_reported() {
  local log status ok=yes
  log="$(ELPI_ORACLE="$tmp/elpi2" LEAN_ELPI="$oracle" "$run" 2>&1)"; status=$?
  [ "$status" -ne 0 ] || ok=no
  grep -q "ELPI 1.18.x is required as oracle, found '2.0.0'" <<<"$log" || ok=no
  grep -q -E '^(pass|FAIL) ' <<<"$log" && ok=no
  check "unexpected oracle version is reported" "$ok"
}

# @tg: verifies:: [[openspec:elpi-conformance#Known divergence register#Registered divergence does not fail the suite]]
test_registered_divergence_does_not_fail() {
  local log status ok=yes
  log="$(LEAN_ELPI="$tmp/reversing" CONFORMANCE_CORPUS="$here/fixtures/corpus" CONFORMANCE_DIVERGENCES="$here/fixtures/divergences.md" "$run" 2>&1)"; status=$?
  grep -q '^known  append (registered divergence)$' <<<"$log" || ok=no
  # Only append prints more than one line, so it is the only program the
  # reversing engine changes; with its entry registered nothing may fail.
  grep -q '^FAIL ' <<<"$log" && ok=no
  [ "$status" -eq 0 ] || ok=no
  check "registered divergence does not fail the suite" "$ok"
}

test_every_program_runs_on_both_engines
test_matching_answers_pass
test_divergent_answers_fail_with_a_diff
test_unexpected_oracle_version_is_reported
test_registered_divergence_does_not_fail
echo "selftest: $failures failure(s)"
[ "$failures" -eq 0 ]
