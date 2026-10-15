#!/usr/bin/env python3
"""Benchmark lean-elpi against ELPI 1.18 (OCaml) and Teyjus on ELPI's own performance programs.

Each workload is ELPI's upstream program (tests/upstream/sources, run as `-test`, the query `main`).
Teyjus runs only the programs that are also valid Teyjus modules (`.mod` + `.sig`).
Every engine runs each workload RUNS times; we record wall time (median, min) and peak
resident memory. A run that exits non-zero or exceeds TIMEOUT counts as a failure and is shown as such.

Usage: tests/bench/run.py [--runs N] [--timeout S] [--only REGEX] [--json out.json]
Environment: ELPI_ORACLE (elpi), LEAN_ELPI (.lake/build/bin/lean-elpi), TEYJUS_BIN (dir with tjcc, tjlink, tjsim).
@lat: [[components#Benchmark harness]]
"""
import argparse, json, os, platform, re, resource, shutil, statistics, subprocess, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SRC = ROOT / "tests" / "upstream" / "sources"

# name, category, ELPI source, Teyjus module (basename in SRC, optional)
WORKLOADS = [
    ("rev", "FO", "rev.elpi", None),
    ("rev14", "FO", "rev14.elpi", "rev14"),
    ("queens", "FO", "queens.elpi", "queens"),
    ("zebra", "FO", "zebra.elpi", "zebra"),
    ("crypt", "FO", "crypt.mod", "crypt"),
    ("ackermann", "FO", "ackermann.elpi", None),
    ("mu", "FO", "mu.mod", "mu"),
    ("fast_mu", "FO", "fast_mu.mod", "fast_mu"),
    ("index2", "FO", "index2.elpi", None),
    ("deep_index", "FO", "deep_indexing.elpi", None),
    ("map_rbtree", "FO", "map.elpi", None),
    ("map_list", "FO", "map_list.elpi", None),
    ("map_list_opt", "FO", "map_list_opt.elpi", None),
    ("map_ho", "FO", "map_ho.elpi", None),
    ("set", "FO", "set.elpi", None),
    ("set_ho", "FO", "set_ho.elpi", None),
    ("dt", "FO", "dt.elpi", None),
    ("dt_off", "FO", "dt_off.elpi", None),
    ("cbv", "HO", "reduce_cbv.elpi", None),
    ("cbn", "HO", "reduce_cbn.elpi", None),
    ("lambda3", "HO", "lambda3.elpi", None),
    # our own, smaller programs (tests/bench/programs): they finish on every engine
    ("nrev400", "FO", "nrev.elpi", None),
    ("fib23", "FO", "fib.elpi", None),
    ("church5", "HO", "hoabs.elpi", None),
]
OWN = ROOT / "tests" / "bench" / "programs"

def timed(cmd, cwd, timeout):
    """Run cmd; return (seconds, peak RSS bytes, exit code or 'timeout')."""
    t0 = time.perf_counter()
    try:
        # Deep first-order recursion (rev, rev14) overflows the default 8 MB stack on every engine; upstream's
        # own benchmark notes run with a larger one, so all engines get the largest the OS allows.
        cmd = ["sh", "-c", 'ulimit -s "$(ulimit -Hs)" 2>/dev/null; exec "$@"', "sh"] + cmd
        p = subprocess.Popen(cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except OSError as e:
        return None, None, f"error: {e}"
    # wait4 gives the child's own rusage, which is what we want for peak memory
    try:
        deadline = t0 + timeout
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if time.perf_counter() > deadline:
                p.kill(); os.wait4(p.pid, 0)
                return timeout, None, "timeout"
            time.sleep(0.002)
    except ChildProcessError:
        return None, None, "error"
    dt = time.perf_counter() - t0
    rss = ru.ru_maxrss if platform.system() == "Darwin" else ru.ru_maxrss * 1024
    return dt, rss, os.waitstatus_to_exitcode(status)

def measure(cmd, cwd, runs, timeout):
    times, rss, code = [], [], 0
    for _ in range(runs):
        dt, mem, rc = timed(cmd, cwd, timeout)
        if rc != 0:
            return {"status": str(rc)}
        times.append(dt); rss.append(mem)
    return {"status": "ok", "median": statistics.median(times), "min": min(times),
            "max": max(times), "rss_mb": max(rss) / 1e6, "runs": runs}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--timeout", type=float, default=120)
    ap.add_argument("--only", default=".")
    ap.add_argument("--json")
    a = ap.parse_args()
    elpi = os.environ.get("ELPI_ORACLE", "elpi")
    lean = os.environ.get("LEAN_ELPI", str(ROOT / ".lake/build/bin/lean-elpi"))
    tj = os.environ.get("TEYJUS_BIN")
    work = Path(tempfile.mkdtemp(prefix="bench-teyjus-"))
    engines = {"elpi": lambda src, mod: [elpi, "-test", "-I", ".", src],
               "lean-elpi": lambda src, mod: [lean, "-test", "-I", ".", src]}
    if tj:
        engines["teyjus"] = lambda src, mod: [f"{tj}/tjsim", "-b", "-e", "1", "-m", "1", "-s", "main.", mod] if mod else None
        for _, _, _, mod in WORKLOADS:
            if mod:
                for ext in ("mod", "sig"):
                    shutil.copy(SRC / f"{mod}.{ext}", work / f"{mod}.{ext}")
                for tool in ("tjcc", "tjlink"):
                    subprocess.run([f"{tj}/{tool}", mod], cwd=work, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    meta = {"machine": platform.platform(), "cpu": subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip() or platform.processor(),
            "elpi": subprocess.run([elpi, "-version"], capture_output=True, text=True).stdout.strip(),
            "runs": a.runs, "timeout": a.timeout, "date": time.strftime("%Y-%m-%d")}
    # startup floor: the cost of loading the engine and running a trivial `main`
    (work / "empty.elpi").write_text("main.\n")
    results = {"meta": meta, "workloads": {}}
    rows = [("startup", "-", "empty.elpi", None)] + [w for w in WORKLOADS if re.search(a.only, w[0])]
    for name, cat, src, mod in rows:
        res = {"category": cat}
        for eng, cmd in engines.items():
            if name == "startup":
                c = cmd(str(work / "empty.elpi"), None)
                r = measure(c, work, a.runs, a.timeout) if c else {"status": "n/a"}
            else:
                c = cmd(src, mod)
                where = work if eng == "teyjus" else OWN if (OWN / src).exists() else SRC
                r = measure(c, where, a.runs, a.timeout) if c else {"status": "n/a"}
            res[eng] = r
        results["workloads"][name] = res
        print(f"{name:12s}", "  ".join(f"{e}={r['median']*1000:.0f}ms" if r['status'] == 'ok' else f"{e}={r['status']}" for e, r in res.items() if e != 'category'), flush=True)
    if a.json:
        Path(a.json).write_text(json.dumps(results, indent=2))
    shutil.rmtree(work, ignore_errors=True)

if __name__ == "__main__":
    main()
