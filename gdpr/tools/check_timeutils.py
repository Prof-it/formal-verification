#!/usr/bin/env python3
"""Differential test of TimeUtils.ToMinutes against Python's datetime.

  python3 check_timeutils.py <dir containing TimeUtils.tla> <tla2tools.jar> [--n 300] [--seed 1]

Reference: minutes since 2020-01-01 00:00 computed with datetime (proleptic Gregorian),
which is exactly what ToMinutes should return (FixedEpochYear = 2020).
Test set: n uniformly random minutes in 2020-01-01 .. 2500-12-31 plus boundary dates
(29 Feb / 1 Mar in leap years, the non-leap 2100, the leap 2400, year ends, horizon).
The expected values are written into a throw-away TLA+ module that EXTENDS the given
TimeUtils; TLC evaluates ToMinutes for every case and prints the indices that differ.
"""
import argparse, datetime as dt, random, re, shutil, subprocess, sys, tempfile
from pathlib import Path

EPOCH = dt.datetime(2020, 1, 1)
BOUNDARY = [dt.datetime(*t) for t in [
    (2020, 1, 1, 0, 0), (2020, 2, 29, 23, 59), (2020, 3, 1, 0, 0), (2020, 12, 31, 23, 59),
    (2021, 1, 1, 0, 0), (2024, 1, 31, 12, 0), (2024, 2, 1, 0, 0), (2024, 2, 29, 23, 59),
    (2024, 3, 1, 0, 0), (2100, 2, 28, 23, 59), (2100, 3, 1, 0, 0), (2400, 2, 29, 0, 0),
    (2400, 3, 1, 0, 0), (2500, 12, 31, 23, 59)]]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tla_dir"); ap.add_argument("jar")
    ap.add_argument("--n", type=int, default=300); ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    # TLC runs inside a temporary directory, so both paths must be absolute
    jar = Path(a.jar).expanduser().resolve()
    tla_dir = Path(a.tla_dir).expanduser().resolve()
    if not jar.is_file():
        sys.exit(f"tla2tools.jar not found: {jar}")
    if not (tla_dir / "TimeUtils.tla").is_file():
        sys.exit(f"TimeUtils.tla not found in {tla_dir}")
    rnd = random.Random(a.seed)
    span = int((dt.datetime(2501, 1, 1) - EPOCH).total_seconds() // 60)
    dates = [EPOCH + dt.timedelta(minutes=rnd.randrange(span)) for _ in range(a.n)] + BOUNDARY
    exp = [int((d - EPOCH).total_seconds() // 60) for d in dates]

    work = Path(tempfile.mkdtemp(prefix="chk_timeutils_"))
    shutil.copy(tla_dir / "TimeUtils.tla", work)
    cases = ",\n  ".join(f"<<T({d.year},{d.month},{d.day},{d.hour},{d.minute}),{m}>>" for d, m in zip(dates, exp))
    (work / "Chk.tla").write_text(f"""---- MODULE Chk ----
EXTENDS TimeUtils
T(y,mo,d,h,mi) == [year|->y, month|->mo, day|->d, hour|->h, minute|->mi]
Cases == <<{cases}>>
Bad == {{i \\in 1..Len(Cases) : ToMinutes(Cases[i][1]) # Cases[i][2]}}
ASSUME PrintT(<<"mismatch_indices", Bad>>)
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
""")
    (work / "Chk.cfg").write_text("CONSTANTS MonthRange = {} DayRange = {} HourRange = {} "
                                  "MinuteRange = {} YearRange = {} FixedEndTime = 0\nINIT Init\nNEXT Next\n")
    res = subprocess.run(["java", "-cp", str(jar), "tlc2.TLC", "-metadir", str(work / "states"), "Chk.tla",
                          "-config", "Chk.cfg"], cwd=work, capture_output=True, text=True)
    out = res.stdout
    m = re.search(r'<<\s*"mismatch_indices",\s*\{(.*?)\}\s*>>', out, re.S)
    if not m:
        sys.exit(f"TLC did not evaluate the cases (exit code {res.returncode}, work dir {work}).\n"
                 f"--- stdout ---\n{out[-2000:]}\n--- stderr ---\n{res.stderr[-2000:]}")
    bad = [int(i) for i in re.findall(r"\d+", m.group(1))]
    print(f"{len(dates)} dates checked, {len(bad)} mismatches")
    for i in bad[:10]:
        d = dates[i - 1]
        print(f"  {d:%Y-%m-%d %H:%M}  expected {exp[i - 1]}")
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
