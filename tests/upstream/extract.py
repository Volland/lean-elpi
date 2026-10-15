#!/usr/bin/env python3
"""Regenerate tests/upstream/{manifest.tsv,sources/,expected/} from an ELPI source tree.

Usage: python3 -I tests/upstream/extract.py <elpi-source-dir>
(e.g. ~/.opam/default/.opam-switch/sources/elpi.1.18.2)

Parses the `declare "name" ...` entries of <dir>/tests/suite/*.ml (the upstream
test registry) and copies <dir>/tests/sources. Entries without an `~source_elpi`
(OCaml API and dune tests) are not runnable by a CLI and are not listed.
"""
import os, re, shutil, sys

src = sys.argv[1]
here = os.path.dirname(os.path.abspath(__file__))
suite = os.path.join(src, "tests", "suite")
for d in ("sources", "expected"):
    shutil.rmtree(os.path.join(here, d), ignore_errors=True)
shutil.copytree(os.path.join(src, "tests", "sources"), os.path.join(here, "sources"),
                ignore=shutil.ignore_patterns("*.ml", "dune", "*.json", "helena_elpi", "ld-3C", "lyp"))  # big corpora and trace references are not vendored
os.makedirs(os.path.join(here, "expected"))
shutil.copy(os.path.join(src, "COPYING") if os.path.exists(os.path.join(src, "COPYING"))
            else os.path.join(src, "LICENSE"), os.path.join(here, "LICENSE-ELPI"))

# quote_syntax.elpi reads "src/builtin.elpi" relative to the upstream tree root
os.makedirs(os.path.join(here, "sources", "src"))
shutil.copy(os.path.join(src, "src", "builtin.elpi"), os.path.join(here, "sources", "src"))

def str_to_ere(p):
    """OCaml Str regexp syntax -> POSIX ERE: groups and alternation are the escaped forms."""
    out, i = [], 0
    while i < len(p):
        c = p[i]
        if c == "\\" and i + 1 < len(p):
            n = p[i + 1]
            out.append({"(": "(", ")": ")", "|": "|"}.get(n, "\\" + n)); i += 2; continue
        out.append("\\" + c if c in "(){}|" else c); i += 1
    return "".join(out)

def unescape(s):
    return s.replace("\\n", "\n").replace('\\"', '"').replace("\\\\", "\\")

rows = []
for fn in sorted(os.listdir(suite)):
    if fn in ("suite.ml", "suite.mli") or not fn.endswith(".ml"):
        continue
    cat = fn[:-3]
    text = open(os.path.join(suite, fn)).read()
    for m in re.finditer(r'declare\s+"([^"]+)"(.*?)\n\s*\(\)', text, re.S):
        name, body = m.group(1), m.group(2)
        def opt(k):
            r = re.search(r"~" + k + r':"([^"]*)"', body)
            return r.group(1) if r else ""
        source = opt("source_elpi")
        if not source:
            continue
        flags = []
        if "~typecheck:false" in body: flags.append("-no-tc")
        if "~legacy_parser:true" in body: flags.append("-legacy-parser")
        if "~outside_llam:true" in body: flags.append("-delay-problems-outside-pattern-fragment")
        skip = ""
        if "~trace:" in body: skip = "needs -trace-on JSON output"
        if "SuccessOutputFile" in body: skip = skip or "compares against a reference trace file"
        if "~deps_teyjus" in body and "teyjus" in body and cat.startswith("perf"): pass
        expect, pat, kind = "success", "", ""
        if re.search(r"~expectation:\s*(Test\.)?Failure\b", body): expect = "failure"
        rx = re.search(r'(Success|Failure)Output\s*\(?\s*(?:Test\.)?\(?Str\.regexp(_string)?\s*"((?:[^"\\]|\\.)*)"\)', body) \
            or re.search(r'(Success|Failure)Output\s*\(?\s*(?:Test\.)?\(?Str\.regexp(_string)?\s*\((.*?)\)\)\)', body, re.S)
        if rx:
            kind = "fixed" if rx.group(2) else "regex"
            raw = rx.group(3)
            q = re.search(r"\{\|(.*?)\|\}", raw, re.S)
            pat = q.group(1) if q else unescape(raw.strip().strip('"'))
            if kind == "regex": pat = str_to_ere(pat)
            expect = "output" if rx.group(1) == "Success" else "failure-output"
            with open(os.path.join(here, "expected", name + ".out"), "w") as f:
                f.write(pat)
        if not skip and not os.path.exists(os.path.join(here, "sources", source)):
            skip = "large source not vendored (set UPSTREAM_SOURCES to the full tests/sources)"
        inp = opt("input")
        rows.append((name, cat, source, expect, kind, ",".join(flags), inp, skip))

with open(os.path.join(here, "manifest.tsv"), "w") as f:
    f.write("# name|category|source|expect|match|flags|input|skip\n")
    for r in rows:
        f.write("|".join(r) + "\n")
print(len(rows), "runnable upstream tests")
