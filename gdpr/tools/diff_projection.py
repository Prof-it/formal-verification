#!/usr/bin/env python3
"""Differential test: whole-log verdict == OR of per-(subject, data) projection verdicts.

  python3 tools/diff_projection.py --jar ../tla_modules/tla2tools.jar [--logs 40] [--seed 7]

Random logs (default: uniform random events, mostly malformed; --wellformed: plausible
per-pair histories): 2-3 (subject, data) pairs, 4-9 events of all seven types, drawn from timestamps
that create ties within and across pairs and that straddle the 72 h boundary (72 h - 1 min,
72 h, 72 h + 1 min). Each invariant is checked in its own TLC run, so that TLC stopping at
the first violation cannot hide a difference. Any mismatch is printed with its log and the
script exits with 1; mismatching logs are also written to --failures.
"""
import argparse
import json
import random
import sys
from datetime import datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_log import EVENT_TYPES, check, validate  # noqa: E402

INVARIANTS = ["NoRejectedEvents", "AllProcessingIsLawful", "BreachReportedOnTime"]
BASE = datetime(2025, 7, 12, 8, 0)
OFFSETS = [timedelta(minutes=m) for m in (0, 0, 1, 1, 2, 5)] + \
          [timedelta(hours=72) + timedelta(minutes=m) for m in (-1, 0, 1, 31)] + \
          [timedelta(days=5)]
# weights: legal-basis and processing events more frequent than contract/breach events
TYPE_WEIGHTS = {"GiveConsent": 4, "WithdrawConsent": 3, "StartProcessing": 4, "StartContract": 1,
                "EndContract": 1, "DataBreachDetected": 2, "DataBreachReported": 2}


def random_log(rnd: random.Random) -> list[dict]:
    pairs = [("a", "d"), ("b", "d"), ("a", "e")][: rnd.choice([2, 3])]
    types = sorted(EVENT_TYPES)
    events = []
    for _ in range(rnd.randint(4, 9)):
        s, d = rnd.choice(pairs)
        typ = rnd.choices(types, [TYPE_WEIGHTS[t] for t in types])[0]
        events.append({"type": typ, "time": (BASE + rnd.choice(OFFSETS)).strftime("%Y-%m-%d %H:%M"),
                       "subject": s, "data": d})
    return events


def wellformed_log(rnd: random.Random, lawful: float = 0.0) -> list[dict]:
    """Per pair a plausible history: consent/contract before withdrawal/end, detection before
    report; timestamps from OFFSETS so that ties across pairs and 72 h boundaries remain."""
    pairs = [("a", "d"), ("b", "d"), ("a", "e")][: rnd.choice([2, 3])]
    events = []
    offs = sorted(set(OFFSETS))
    for s, d in pairs:
        def add(typ, k):
            events.append({"type": typ, "time": (BASE + offs[k]).strftime("%Y-%m-%d %H:%M"),
                           "subject": s, "data": d})
        if rnd.random() < lawful:
            # processing strictly after a basis that is never withdrawn, so AllProcessingIsLawful
            # holds for this pair (a same-minute tie would be a violation under the conservative
            # semantics); ties with OTHER pairs remain possible
            b0 = rnd.randrange(0, 3)
            add(rnd.choice(["GiveConsent", "StartContract"]), b0)
            add("StartProcessing", rnd.randrange(b0 + 1, b0 + 3))
            if rnd.random() < 0.5:
                k = rnd.randrange(0, 3)
                add("DataBreachDetected", k)
                add("DataBreachReported", rnd.randrange(k, len(offs)))
            continue
        basis = rnd.choice(["GiveConsent", "StartContract", None])
        b0 = rnd.randrange(0, 3)
        if basis:
            add(basis, b0)
            if rnd.random() < 0.5:
                add("WithdrawConsent" if basis == "GiveConsent" else "EndContract",
                    rnd.randrange(b0, len(offs)))
        if rnd.random() < 0.8:
            add("StartProcessing", rnd.randrange(0, 4))
        if rnd.random() < 0.5:
            k = rnd.randrange(0, 3)
            add("DataBreachDetected", k)
            if rnd.random() < 0.7:
                add("DataBreachReported", rnd.randrange(k, len(offs)))
    return events


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jar", required=True)
    ap.add_argument("--logs", type=int, default=40)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--wellformed", action="store_true",
                    help="generate plausible per-pair histories instead of uniform random events")
    ap.add_argument("--lawful", type=float, default=0.0,
                    help="with --wellformed: fraction of pairs whose processing is lawful throughout")
    ap.add_argument("--failures", type=Path, default=Path("projection_failures.json"))
    a = ap.parse_args()
    jar = Path(a.jar).expanduser().resolve()
    rnd = random.Random(a.seed)

    mismatches, tally = [], {inv: {"violated": 0, "holds": 0} for inv in INVARIANTS}
    for i in range(a.logs):
        raw = wellformed_log(rnd, a.lawful) if a.wellformed else random_log(rnd)
        import io, contextlib
        with contextlib.redirect_stderr(io.StringIO()):      # duplicate warnings are expected
            events = validate(raw)
        for inv in INVARIANTS:
            full = check(events, jar, [inv], project=False)[0]["verdict"]
            parts = check(events, jar, [inv], project=True, jobs=a.jobs)
            proj = "violated" if any(r["verdict"] == "violated" for r in parts) else "holds"
            tally[inv][full] += 1
            if full != proj:
                mismatches.append({"log": raw, "invariant": inv, "full": full, "projected": proj})
                print(f"MISMATCH log {i} {inv}: full={full} projected={proj}\n  {json.dumps(raw)}")
        print(f"log {i + 1}/{a.logs}: {len(events)} events, "
              f"{len({(e['subject'], e['data']) for e in events})} pairs", flush=True)

    print("\nverdict distribution (whole log):")
    for inv, c in tally.items():
        print(f"  {inv:<24} violated {c['violated']:>3}  holds {c['holds']:>3}")
    if mismatches:
        a.failures.write_text(json.dumps(mismatches, indent=2))
        print(f"{len(mismatches)} MISMATCHES, written to {a.failures}")
        sys.exit(1)
    print(f"0 mismatches in {a.logs * len(INVARIANTS)} comparisons")


if __name__ == "__main__":
    main()
