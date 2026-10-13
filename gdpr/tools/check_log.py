#!/usr/bin/env python3
"""Check an event log against GDPR_Rules with TLC, optionally per (subject, data) projection.

Input (one of):
  log.json                       JSON list of events:
                                   {"type": "GiveConsent", "time": "2025-07-12 08:20",
                                    "subject": "erni", "data": "emaildata"}
  --scenario MC_ObervedEventX    an event set defined in MC_GDPR_Time.tla

Modes:
  default        one TLC run per (subject, data) pair, run in parallel (--jobs)
  --no-project   one TLC run over the whole log

Why projection is allowed: every invariant in GDPR_Rules relates only events and records of
the same (subject, data) pair (legal bases, processes, breaches and the rejection of an event
are all matched on subject and data). Projection removes the interleavings between
simultaneous events of DIFFERENT pairs, which cannot change any of these verdicts.
This argument no longer holds once a property relates several pairs; then use --no-project.
tools/diff_projection.py tests the equivalence on random logs.

Differences in what is reported:
  * TLC stops at the first violation of a run. Without projection you therefore get one
    violation for the whole log; with projection you get one per violating pair.
  * The violating STATE can differ: in the full log, an unrelated event may advance `now`
    past a deadline earlier; in the projection the same violation is found at the next event
    of the pair or at the observation horizon. The verdict is the same.

Usage:
  python3 tools/check_log.py log.json --jar ../tla_modules/tla2tools.jar
  python3 tools/check_log.py --scenario MC_ObervedEventDeadlineViolation --jar ... --traces out/
  python3 tools/check_log.py log.json --jar ... --no-project --invariants AllProcessingIsLawful

Exit code: 0 all invariants hold, 1 at least one violation, 2 usage or TLC error.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path

GDPR_DIR = Path(__file__).resolve().parent.parent
BASE_MODULES = ["TimeUtils.tla", "GDPR_Time.tla", "GDPR_Rules.tla", "MC_GDPR_Time.tla"]
EVENT_TYPES = {"StartProcessing", "GiveConsent", "WithdrawConsent", "StartContract",
               "EndContract", "DataBreachDetected", "DataBreachReported"}
DEFAULT_INVARIANTS = ["NoRejectedEvents", "AllProcessingIsLawful", "BreachReportedOnTime",
                      "TypeInvariant"]
EPOCH_YEAR, HORIZON_YEAR = 2020, 2500     # FixedEpochYear in TimeUtils, MC_MAX_TIME in MC_GDPR_Time


# ------------------------------------------------------------------ input

def parse_time(s: str) -> datetime:
    for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%dT%H:%M", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            t = datetime.strptime(s, fmt)
        except ValueError:
            continue
        if t.second:
            raise ValueError(f"{s}: the model has minute resolution; seconds must be 0")
        return t
    raise ValueError(f"unsupported time format: {s!r} (use 'YYYY-MM-DD HH:MM', UTC)")


def validate(events: list[dict]) -> list[dict]:
    out, seen = [], set()
    for i, e in enumerate(events):
        missing = {"type", "time", "subject", "data"} - e.keys()
        if missing:
            raise ValueError(f"event {i}: missing fields {sorted(missing)}")
        if e["type"] not in EVENT_TYPES:
            raise ValueError(f"event {i}: unknown type {e['type']!r}")
        t = e["time"] if isinstance(e["time"], datetime) else parse_time(e["time"])
        if not EPOCH_YEAR <= t.year <= HORIZON_YEAR:
            raise ValueError(f"event {i}: year {t.year} outside {EPOCH_YEAR}..{HORIZON_YEAR}")
        for f in ("subject", "data"):
            if not re.fullmatch(r"[A-Za-z0-9_.@:+\- ]+", str(e[f])):
                raise ValueError(f"event {i}: {f} {e[f]!r} contains unsupported characters")
        key = (e["type"], t, str(e["subject"]), str(e["data"]))
        if key in seen:
            print(f"warning: duplicate event {key[0]} {t:%Y-%m-%d %H:%M} {key[2]}/{key[3]} "
                  f"is merged (ObservedEvents is a set)", file=sys.stderr)
            continue
        seen.add(key)
        out.append({"type": key[0], "time": t, "subject": key[2], "data": key[3]})
    if not out:
        raise ValueError("empty log")
    return out


def load_json(path: Path) -> list[dict]:
    doc = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(doc, dict):
        doc = doc.get("events", [])
    return validate(doc)


def load_scenario(name: str, module: Path) -> list[dict]:
    """Read an event set `name == { [...], ... }` from MC_GDPR_Time.tla."""
    text = re.sub(r"\\\*[^\n]*", "", module.read_text(encoding="utf-8"))   # drop \* comments
    m = re.search(rf"^{re.escape(name)}\s*==\s*\{{(.*?)\n\s*\}}", text, re.S | re.M)
    if not m:
        raise ValueError(f"event set {name} not found in {module}")
    events = []
    for rec in re.finditer(r"\[\s*type\s*\|->\s*\"(\w+)\"\s*,\s*time\s*\|->\s*\[(.*?)\]\s*,"
                           r"\s*subject\s*\|->\s*\"([^\"]+)\"\s*,\s*data\s*\|->\s*\"([^\"]+)\"\s*\]",
                           m.group(1), re.S):
        kv = dict(re.findall(r"(year|month|day|hour|minute)\s*\|->\s*(\d+)", rec.group(2)))
        t = datetime(*(int(kv[k]) for k in ("year", "month", "day", "hour", "minute")))
        events.append({"type": rec.group(1), "time": t, "subject": rec.group(3), "data": rec.group(4)})
    return validate(events)


# ------------------------------------------------------------------ TLC

def tla_event(e: dict) -> str:
    t = e["time"]
    return (f'[type |-> "{e["type"]}", time |-> [year |-> {t.year}, month |-> {t.month}, '
            f'day |-> {t.day}, hour |-> {t.hour}, minute |-> {t.minute}], '
            f'subject |-> "{e["subject"]}", data |-> "{e["data"]}"]')


def write_model(work: Path, events: list[dict], invariants: list[str]) -> None:
    for m in BASE_MODULES:
        shutil.copy(GDPR_DIR / m, work / m)
    subs = sorted({e["subject"] for e in events})
    dats = sorted({e["data"] for e in events})
    (work / "Log.tla").write_text(
        "---- MODULE Log ----\nEXTENDS MC_GDPR_Time\n"
        "LogSubjects == {" + ", ".join(f'"{s}"' for s in subs) + "}\n"
        "LogData == {" + ", ".join(f'"{d}"' for d in dats) + "}\n"
        "LogEvents == {\n  " + ",\n  ".join(tla_event(e) for e in events) + "\n}\n====\n")
    (work / "Log.cfg").write_text(
        "SPECIFICATION Spec\nCONSTANTS\n"
        "    DataSubjects <- LogSubjects\n    Data <- LogData\n    ObservedEvents <- LogEvents\n"
        "    YearRange <- MC_YearRange\n    MonthRange <- MC_MonthRange\n    DayRange <- MC_DayRange\n"
        "    HourRange <- MC_HourRange\n    MinuteRange <- MC_MinuteRange\n"
        "    FixedEndTime <- MC_MAX_TIME\n"
        + "".join(f"INVARIANT {inv}\n" for inv in invariants))


def run_tlc(label: str, events: list[dict], invariants: list[str], jar: Path, workers: int,
            trace_dir: Path | None, timeout: int) -> dict:
    work = Path(tempfile.mkdtemp(prefix="check_log_"))
    try:
        write_model(work, events, invariants)
        cmd = ["java", "-XX:+UseParallelGC", "-cp", str(jar), "tlc2.TLC", "-noGenerateSpecTE", "-workers", str(workers),
               "-metadir", str(work / "states"), "Log.tla", "-config", "Log.cfg"]
        trace_file = None
        if trace_dir is not None:
            trace_file = trace_dir / f"{re.sub(r'[^A-Za-z0-9_.-]', '_', label)}.json"
            i = cmd.index("Log.tla")                      # options go before the spec file
            cmd[i:i] = ["-dumpTrace", "json", str(trace_file)]
        t0 = time.time()
        try:
            res = subprocess.run(cmd, cwd=work, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return {"label": label, "events": len(events), "verdict": "timeout",
                    "invariant": None, "states": None, "seconds": timeout}
        out = res.stdout
        # final summary line only; Progress(...) lines also mention "distinct states found"
        states = re.findall(r"([\d,]+) distinct states found, [\d,]+ states left on queue", out)
        viol = re.search(r"Invariant (\w+) is violated", out)
        if viol:
            verdict = "violated"
        elif "No error has been found" in out:
            verdict = "holds"
        else:
            unknown = re.search(r"Unknown operator: `(\w+)'|The invariant (\w+) .*? not", out)
            raise RuntimeError(f"[{label}] TLC failed (exit {res.returncode}):\n{out[-1500:]}"
                               + ("\nIs the 'reject' fix applied? NoRejectedEvents is missing."
                                  if unknown and "NoRejectedEvents" in out else ""))
        return {"label": label, "events": len(events), "verdict": verdict,
                "invariant": viol.group(1) if viol else None,
                "states": int(states[-1].replace(",", "")) if states else None,
                "seconds": round(time.time() - t0, 2),
                "trace": str(trace_file) if viol and trace_file else None}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def projections(events: list[dict]) -> dict[tuple[str, str], list[dict]]:
    parts: dict[tuple[str, str], list[dict]] = {}
    for e in events:
        parts.setdefault((e["subject"], e["data"]), []).append(e)
    return dict(sorted(parts.items()))


def check(events: list[dict], jar: Path, invariants: list[str], project: bool = True,
          jobs: int = 4, workers: int = 1, trace_dir: Path | None = None,
          timeout: int = 600) -> list[dict]:
    if trace_dir is not None:
        trace_dir.mkdir(parents=True, exist_ok=True)
    if not project:
        return [run_tlc("full_log", events, invariants, jar, workers, trace_dir, timeout)]
    parts = projections(events)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futs = [pool.submit(run_tlc, f"{s}__{d}", evs, invariants, jar, workers, trace_dir, timeout)
                for (s, d), evs in parts.items()]
        return [f.result() for f in futs]


# ------------------------------------------------------------------ CLI

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", nargs="?", type=Path, help="JSON event log")
    ap.add_argument("--scenario", help="event set name in MC_GDPR_Time.tla instead of a JSON log")
    ap.add_argument("--jar", required=True, help="path to tla2tools.jar")
    ap.add_argument("--no-project", action="store_true", help="check the whole log in one TLC run")
    ap.add_argument("--invariants", default=",".join(DEFAULT_INVARIANTS),
                    help=f"comma-separated, checked in this order (default: {','.join(DEFAULT_INVARIANTS)})")
    ap.add_argument("--jobs", type=int, default=4, help="parallel TLC runs (projection mode)")
    ap.add_argument("--workers", type=int, default=1, help="TLC worker threads per run")
    ap.add_argument("--traces", type=Path, help="directory for JSON counterexamples (input for trace2tikz)")
    ap.add_argument("--summary", type=Path, help="write the results as JSON")
    ap.add_argument("--timeout", type=int, default=600, help="seconds per TLC run")
    a = ap.parse_args()

    jar = Path(a.jar).expanduser().resolve()
    if not jar.is_file():
        sys.exit(f"tla2tools.jar not found: {jar}")
    missing = [m for m in BASE_MODULES if not (GDPR_DIR / m).is_file()]
    if missing:
        sys.exit(f"model modules not found in {GDPR_DIR}: {missing}")
    try:
        if a.scenario:
            events = load_scenario(a.scenario, GDPR_DIR / "MC_GDPR_Time.tla")
        elif a.log:
            events = load_json(a.log)
        else:
            sys.exit("give a JSON log or --scenario NAME")
        invariants = [i for i in a.invariants.split(",") if i]
        t0 = time.time()
        results = check(events, jar, invariants, not a.no_project, a.jobs, a.workers,
                        a.traces.resolve() if a.traces else None, a.timeout)
    except (ValueError, RuntimeError) as err:
        print(f"error: {err}", file=sys.stderr)
        sys.exit(2)

    mode = "whole log" if a.no_project else f"{len(results)} (subject, data) projections"
    print(f"{len(events)} events, {mode}, invariants: {', '.join(invariants)}")
    print(f"{'run':<32} {'events':>6} {'states':>9} {'time':>7}  verdict")
    for r in results:
        v = r["verdict"] + (f" ({r['invariant']})" if r["invariant"] else "")
        print(f"{r['label']:<32} {r['events']:>6} {r['states'] if r['states'] is not None else '-':>9} "
              f"{r['seconds']:>6}s  {v}")
    print(f"total wall time {time.time() - t0:.1f}s")
    if a.summary:
        a.summary.write_text(json.dumps({"mode": "full" if a.no_project else "projected",
                                         "invariants": invariants, "results": results}, indent=2))
    if any(r["verdict"] == "timeout" for r in results):
        sys.exit(2)
    sys.exit(1 if any(r["verdict"] == "violated" for r in results) else 0)


if __name__ == "__main__":
    main()
