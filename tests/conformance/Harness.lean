import TestUtil
open TestUtil

/-!
The conformance harness is tested by `tests/conformance/selftest.sh`, which drives
`run.sh` with stand-in engines (the oracle itself, a reversing engine and a fake
oracle). The scenarios are annotated in the script; this file runs it as part of
`lake test` and fails on any `FAIL` line.
-/

#eval show IO Unit from do
  let out ← IO.Process.output { cmd := "bash", args := #["tests/conformance/selftest.sh"] }
  unless out.exitCode == 0 do
    fail s!"selftest failed ({out.exitCode}):\n{out.stdout}\n{out.stderr}"
  check (!(hasSub out.stdout "FAIL")) s!"selftest reported failures:\n{out.stdout}"
  for name in ["every corpus program runs on both engines", "matching answers pass",
      "divergent answers fail with a diff", "unexpected oracle version is reported",
      "registered divergence does not fail the suite"] do
    check (hasSub out.stdout ("ok    " ++ name)) s!"missing selftest result: {name}\n{out.stdout}"
