#!/usr/bin/env python3
"""Re-score the TLC-passing DDMR-26 specs under TypeOK + DDMR26.

Run from the agentic_loop/ directory (or pass --results explicitly):

  python scripts/rescore_with_paper_cfg.py --jar /path/to/tla2tools.jar

For every trial whose final spec passed TLC in the released run, this
  (1) re-runs TLC with the cfg the pipeline actually used (autofill cfg), and
  (2) re-runs TLC with SPECIFICATION Spec / INVARIANTS TypeOK DDMR26 /
      CHECK_DEADLOCK FALSE (+ the CONSTANT lines of the original cfg).
Per-trial TLC output of run (2) is kept in <workdir>/tNN/paper.out.
"""
import argparse, csv, json, os, re, shutil, subprocess, sys
from collections import Counter
from pathlib import Path


def run_tlc(java, jar, workdir, module, cfg, timeout):
    cmd = [java, "-cp", str(jar), "tlc2.TLC", "-workers", "1", "-config", cfg, module]
    try:
        p = subprocess.run(cmd, cwd=workdir, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", None, ""
    out = p.stdout + p.stderr
    m = re.search(r"Invariant (\w+) is violated", out)
    if "No error has been found" in out:
        status = "PASS"
    elif m:
        status = "INV_VIOLATED:" + m.group(1)
    elif "Error:" in out or "error" in out.lower():
        e = re.search(r"Error:[^\n]*", out)
        status = "ERR:" + (e.group(0)[:70] if e else "other")
    else:
        status = "UNKNOWN"
    s = re.search(r"(\d+) distinct states found", out)
    return status, (int(s.group(1)) if s else None), out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jar", default=os.environ.get("TLA_JAR"),
                    help="path to tla2tools.jar (or set env TLA_JAR)")
    ap.add_argument("--results", default="results/comparison/nasa_ddmr26_sample",
                    help="results dir containing case_metrics.csv, baseline/, loop/")
    ap.add_argument("--out", default="rescoring_passes.csv")
    ap.add_argument("--workdir", default="rescore_work")
    ap.add_argument("--java", default="java")
    ap.add_argument("--timeout", type=int, default=120)
    a = ap.parse_args()
    if not a.jar or not Path(a.jar).is_file():
        sys.exit("tla2tools.jar not found: pass --jar or set TLA_JAR")
    R, jar, W = Path(a.results), Path(a.jar).resolve(), Path(a.workdir)

    with open(R / "case_metrics.csv", newline="") as f:
        base = {int(r["case_id"].split("_")[1]): r["TerminalStatus"]
                for r in csv.DictReader(f) if r["mode"] == "baseline"}

    rows = []
    for t, status in sorted(base.items()):
        if status == "success":
            d, att, arm = R / "baseline" / f"trial_{t:02d}", 1, "baseline"
        else:
            rj = R / "loop" / f"trial_{t:02d}" / "nasa_ddmr26_run.json"
            if not rj.is_file():
                continue
            if json.load(open(rj))["attempts"][-1]["status"] != "success":
                continue
            d, att, arm = rj.parent, 2, "repair"
        mod = f"CLA_Generated_attempt_{att}"
        w = W / f"t{t:02d}"
        w.mkdir(parents=True, exist_ok=True)
        shutil.copy(d / "modules" / f"{mod}.tla", w)
        cfg0 = d / "modules" / f"{mod}.autofill_{att}.cfg"   # cfg TLC really used
        if not cfg0.exists():
            cfg0 = d / "modules" / f"{mod}.cfg"
        orig = cfg0.read_text()
        (w / "orig.cfg").write_text(orig)
        consts = [l for l in orig.splitlines() if l.strip().startswith("CONSTANT")]
        (w / "paper.cfg").write_text(
            "SPECIFICATION Spec\nINVARIANTS\n    TypeOK\n    DDMR26\nCHECK_DEADLOCK FALSE\n"
            + "\n".join(consts) + "\n")
        r0 = run_tlc(a.java, jar, w, mod, "orig.cfg", a.timeout)
        r1 = run_tlc(a.java, jar, w, mod, "paper.cfg", a.timeout)
        (w / "paper.out").write_text(r1[2])
        rows.append((t, arm, r0[0], r0[1], r1[0], r1[1]))
        print(f"trial {t:3d} {arm:8s} released-cfg={r0[0]:8s} paper-cfg={r1[0]}", flush=True)

    with open(a.out, "w", newline="") as f:
        w_ = csv.writer(f)
        w_.writerow(["trial", "arm", "released_cfg_result", "states_released",
                     "paper_cfg_result", "states_paper"])
        w_.writerows(rows)

    ini = sum(1 for r in rows if r[1] == "baseline" and r[4] == "PASS")
    res = sum(1 for r in rows if r[1] == "repair" and r[4] == "PASS")
    print("\nreleased cfg :", Counter((r[1], r[2]) for r in rows))
    print("paper cfg    :", Counter((r[1], r[4]) for r in rows))
    print(f"PP initial={ini}  rescued={res}/80  final={ini + res}")
    print("DDMR26 violations:", sorted(r[0] for r in rows if r[4].startswith("INV")))


if __name__ == "__main__":
    main()