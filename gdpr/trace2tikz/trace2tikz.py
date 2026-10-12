#!/usr/bin/env python3
"""
trace2tikz.py -- deterministic TLC counterexample -> TikZ timeline (no LLM, no hand editing).

Input : the JSON trace TLC writes with `-dumpTrace json <file>` (TLC >= 1.8).
Output: a standalone LaTeX/TikZ file that compiles to a vector PDF sized for one
        IEEE column, plus (optionally) a machine-readable summary of what was drawn.

Everything in the figure is computed from the trace:
  * event milestones   = events consumed between consecutive states (events_i \\ events_{i+1})
  * legal-basis bars    = legalBases records (start/end) of the final state
  * processing bars     = processes records of the final state (open end = still running)
  * breach bars         = breaches records (detected -> reported, or -> violating state)
  * unlawful interval   = processing time not covered by any matching legal basis
                          (inclusive bounds, identical to TimeBetween in TimeUtils.tla)
  * 72 h deadline       = detection time + 72 h (Art. 33(1) GDPR, as in Within72Hours)
  * violation marker    = `now` of the last state, i.e. the state in which TLC reports
                          the invariant violation

The horizontal axis is ORDINAL: each distinct time point gets one equally wide slot and
is labelled with its real timestamp. This is stated in the figure ("event-ordered axis")
so that a 5-minute gap and a 3-day gap are not mistaken for proportional durations.

Usage:
  java -cp tla2tools.jar tlc2.TLC MC_GDPR_Time.tla -config MC_ConsentWithdrawn.cfg \\
       -dumpTrace json MC_ConsentWithdrawn.json
  python3 trace2tikz.py MC_ConsentWithdrawn.json --invariant AllProcessingIsLawful \\
       --title "Consent withdrawn" -o MC_ConsentWithdrawn.tex
  pdflatex MC_ConsentWithdrawn.tex
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path

DEADLINE = timedelta(hours=72)

# ---------------------------------------------------------------- trace parsing


def tp(rec: dict) -> datetime:
    """TLA+ TimePoint record -> datetime (proleptic Gregorian, exact)."""
    return datetime(rec["year"], rec["month"], rec["day"], rec["hour"], rec["minute"])


def load_states(path: Path) -> list[dict]:
    """Return the ordered list of states of a TLC JSON counterexample."""
    doc = json.loads(path.read_text(encoding="utf-8"))
    ce = doc.get("counterexample")
    if ce is None:
        sys.exit(f"{path}: no counterexample (the property holds; nothing to visualise)")
    states: dict[int, dict] = {}
    for step in ce["action"]:
        (i, s_i), _act, (j, s_j) = step
        states[i], states[j] = s_i, s_j
    for (i, s) in ce.get("state", []) or []:   # single-state traces (violation in Init)
        states[i] = s
    if not states:
        sys.exit(f"{path}: empty counterexample")
    return [states[k] for k in sorted(states)]


def ev_key(e: dict) -> tuple:
    return (e["type"], tp(e["time"]), e["subject"], e["data"])


@dataclass
class Bar:
    lane: str
    start: datetime
    end: datetime | None        # None = open (still active at the violating state)
    style: str


@dataclass
class Mark:
    time: datetime
    label: str
    style: str


def extract(states: list[dict], invariant: str, horizon: datetime | None):
    final = states[-1]
    t_viol = tp(final["now"])

    # 1. events consumed between consecutive states, in trace order
    events: list[tuple[datetime, str, int]] = []
    for k in range(len(states) - 1):
        before = {ev_key(e) for e in states[k]["events"]}
        after = {ev_key(e) for e in states[k + 1]["events"]}
        for (typ, t, subj, dat) in sorted(before - after, key=lambda x: x[1]):
            events.append((t, typ, k + 2))  # TLC numbers states from 1

    bars: list[Bar] = []
    marks: list[Mark] = []

    def is_open(t: datetime) -> bool:
        return horizon is not None and t == horizon

    # 2. legal bases
    for lb in final["legalBases"]:
        s, e = tp(lb["start"]), tp(lb["end"])
        lane = f'{lb["type"]} ({lb["subject"]}, {lb["data"]})'
        n = sum(1 for b in bars if b.lane.startswith(lane))
        bars.append(Bar(lane if n == 0 else f"{lane} #{n + 1}", s,
                        None if is_open(e) else e, "basis"))

    # 3. processing + unlawful sub-intervals
    for p in final["processes"]:
        lane = f'Processing ({p["subject"]}, {p["data"]})'
        s, e = tp(p["start"]), tp(p["end"])
        e_eff = None if is_open(e) else e
        bars.append(Bar(lane, s, e_eff, "proc"))
        if invariant == "AllProcessingIsLawful":
            cover = sorted((tp(l["start"]), tp(l["end"])) for l in final["legalBases"]
                           if l["subject"] == p["subject"] and l["data"] == p["data"])
            hi = min(t_viol, e)
            # uncovered parts of [s, hi]; bounds of a basis are lawful (inclusive TimeBetween)
            cur = s
            for (ls, le) in cover:
                if le < cur:
                    continue
                if ls > cur:
                    bars.append(Bar(lane, cur, min(ls, hi), "unlawful"))
                cur = max(cur, le)
                if cur >= hi:
                    break
            if cur < hi or (cur == hi == s):   # zero-length only if processing is unlawful from its first instant
                bars.append(Bar(lane, cur, hi, "unlawful"))   # may be zero-length -> stub

    # 4. breaches
    for b in final["breaches"]:
        ev = b["event"]
        lane = f'Breach ({ev["subject"]}, {ev["data"]})'
        t_det = tp(ev["time"])
        dl = t_det + DEADLINE
        if b["status"] == "Reported":
            # the report event matching this breach is the one consumed in the trace
            rep = [t for (t, typ, _) in events if typ == "DataBreachReported" and t >= t_det]
            t_end = min(rep) if rep else t_viol
        else:
            t_end = t_viol
        bars.append(Bar(lane, t_det, t_end, "breach"))
        if invariant == "BreachReportedOnTime" and t_end > dl:
            bars.append(Bar(lane, dl, t_end, "overdue"))
        marks.append(Mark(dl, r"72\,h deadline", "deadline"))

    marks.append(Mark(t_viol, f"violation ({invariant}, state {len(states)})", "violation"))
    return events, bars, marks, t_viol


# ---------------------------------------------------------------- TikZ emission

TEX_HEADER = r"""\documentclass[tikz,border=1pt]{standalone}
\usepackage{mathptmx}  % Times, as in the paper preamble
\usetikzlibrary{patterns,arrows.meta,shapes.geometric}
\begin{document}
\footnotesize
\begin{tikzpicture}[x=@SLOT@cm,y=-0.62cm,
  lane/.style={anchor=east,font=\footnotesize},
  basis/.style={fill=black!18,draw=black!70},
  proc/.style={fill=black!6,draw=black!70},
  breach/.style={fill=black!6,draw=black!70},
  unlawful/.style={pattern=north east lines,pattern color=red!80!black,draw=red!80!black,thick},
  overdue/.style={pattern=north east lines,pattern color=red!80!black,draw=red!80!black,thick},
  ev/.style={fill=black,draw=black,diamond,inner sep=1.4pt},
  tick/.style={font=\scriptsize,align=center,anchor=north,inner sep=1pt}]
"""


def tex_escape(s: str) -> str:
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_")
             .replace("&", r"\&").replace("%", r"\%").replace("#", r"\#"))


def fmt(t: datetime, horizon: datetime | None) -> str:
    if horizon is not None and t == horizon:
        return r"end of\\horizon"
    return t.strftime("%m-%d\\\\%H:%M")


def render(events, bars, marks, t_viol, title: str, horizon: datetime | None,
           width_cm: float) -> str:
    # ordinal axis over every time point that is actually drawn
    pts = {t for (t, _, _) in events} | {m.time for m in marks}
    for b in bars:
        pts.add(b.start)
        if b.end is not None:
            pts.add(b.end)
    pts = sorted(pts)
    pos = {t: i for i, t in enumerate(pts)}
    x_open = len(pts) - 0.35          # where open-ended bars stop (arrow)
    n_slots = len(pts)
    slot = round(width_cm / max(n_slots, 4), 3)

    # if the trace concerns a single (subject, data) pair, move it into the title
    import re
    pairs = {m.group(1) for b in bars for m in [re.search(r"\((.*?)\)", b.lane)] if m}
    if len(pairs) == 1:
        pair = pairs.pop()
        for b in bars:
            b.lane = b.lane.replace(f" ({pair})", "")
        title = f"{title} \u2014 subject {pair.split(', ')[0]}, data {pair.split(', ')[1]}" if title else ""
    lanes = ["Events"]
    for b in bars:
        if b.lane not in lanes:
            lanes.append(b.lane)
    row = {l: i for i, l in enumerate(lanes)}

    out = [TEX_HEADER.replace("@SLOT@", str(slot))]
    if title:
        out.append(r"\node[anchor=south west,font=\small\bfseries] at (-0.2,-1.25) {%s};"
                   % tex_escape(title).replace('\u2014', '---'))
    # grid
    for t, i in pos.items():
        out.append(r"\draw[black!15] (%d,-0.45) -- (%d,%0.2f);" % (i, i, len(lanes) - 0.5))
        out.append(r"\node[tick] at (%d,%0.2f) {%s};" % (i, len(lanes) - 0.4, fmt(t, horizon)))
    # lane labels and separators
    for l, r in row.items():
        out.append(r"\node[lane] at (-0.3,%d) {%s};" % (r, tex_escape(l)))
    # bars (drawn in order so that hatched overlays sit on top)
    order = {"basis": 0, "proc": 0, "breach": 0, "unlawful": 1, "overdue": 1}
    for b in sorted(bars, key=lambda b: order[b.style]):
        r = row[b.lane]
        x0 = pos[b.start]
        x1 = pos[b.end] if b.end is not None else x_open
        if x1 == x0:                       # violation at the instant processing starts
            x1 = x0 + 0.3
        out.append(r"\draw[%s] (%0.2f,%0.2f) rectangle (%0.2f,%0.2f);"
                   % (b.style, x0, r - 0.28, x1, r + 0.28))
        if b.end is None and b.style in ("basis", "proc"):
            out.append(r"\draw[-{Stealth[length=3pt]},black!70] (%0.2f,%d) -- ++(0.3,0);"
                       % (x1, r))
    # event milestones with type label (staggered to avoid overlap)
    for k, (t, typ, sidx) in enumerate(events):
        x = pos[t]
        out.append(r"\node[ev] at (%d,0) {};" % x)
        out.append(r"\node[font=\scriptsize,anchor=south west,rotate=35,inner sep=1pt] "
                   r"at (%0.2f,-0.2) {%s};" % (x - 0.05, tex_escape(typ)))
    # vertical markers
    for m in marks:
        x = pos[m.time]
        if m.style == "deadline":
            out.append(r"\draw[dashed,black] (%d,-0.45) -- (%d,%0.2f);" % (x, x, len(lanes) - 0.5))
        else:
            out.append(r"\draw[red!80!black,thick] (%d,-0.45) -- (%d,%0.2f);"
                       % (x, x, len(lanes) - 0.5))
    # legend
    ly = len(lanes) + 0.95
    used = {b.style for b in bars} | {m.style for m in marks}
    items = [r"\tikz[x=1cm,y=1cm]\node[ev]{}; event"]
    if "basis" in used:
        items.append(r"\tikz[x=1cm,y=1cm]\draw[basis](0,0)rectangle(.35,.18); legal basis")
    if used & {"proc", "breach"}:
        items.append(r"\tikz[x=1cm,y=1cm]\draw[proc](0,0)rectangle(.35,.18); processing / open breach")
    if used & {"unlawful", "overdue"}:
        items.append(r"\tikz[x=1cm,y=1cm]\draw[unlawful](0,0)rectangle(.35,.18); violating interval")
    if "deadline" in used:
        items.append(r"\tikz[x=1cm,y=1cm]\draw[dashed](0,0)--(0,.2); 72\,h deadline")
    items.append(r"\tikz[x=1cm,y=1cm]\draw[red!80!black,thick](0,0)--(0,.2); violating state")
    items.append(r"\tikz[x=1cm,y=1cm]\draw[-{Stealth[length=3pt]}](0,.1)--(.3,.1); still active")
    out.append(r"\node[anchor=north west,font=\scriptsize,text width=%0.2fcm,xshift=-1.5cm] at (0,%0.2f) {%s};"
               % (width_cm + 1.5, ly, r"\hspace{0.8em plus 1em} ".join(r"\mbox{%s}" % i for i in items)
                  + r"\par\smallskip\textit{Event-ordered axis: equal spacing; labels give real "
                    r"timestamps (MM-DD HH:MM).}"))
    out.append(r"\end{tikzpicture}")
    out.append(r"\end{document}")
    return "\n".join(out) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("trace", type=Path, help="TLC JSON trace (-dumpTrace json)")
    ap.add_argument("--invariant", required=True,
                    choices=["AllProcessingIsLawful", "BreachReportedOnTime"])
    ap.add_argument("--title", default="")
    ap.add_argument("--horizon", default="2500-12-31 23:59",
                    help="FixedEndTime of the model (drawn as an open end)")
    ap.add_argument("--width-cm", type=float, default=6.0,
                    help="width of the plotting area (column width minus lane labels)")
    ap.add_argument("-o", type=Path, required=True)
    ap.add_argument("--summary", type=Path, help="optional JSON summary of drawn elements")
    a = ap.parse_args()

    horizon = datetime.strptime(a.horizon, "%Y-%m-%d %H:%M") if a.horizon else None
    states = load_states(a.trace)
    events, bars, marks, t_viol = extract(states, a.invariant, horizon)
    a.o.write_text(render(events, bars, marks, t_viol, a.title, horizon, a.width_cm))
    if a.summary:
        a.summary.write_text(json.dumps({
            "states": len(states),
            "violation_time": str(t_viol),
            "events": [(str(t), typ, s) for (t, typ, s) in events],
            "bars": [(b.lane, str(b.start), str(b.end), b.style) for b in bars],
            "marks": [(str(m.time), m.label) for m in marks],
        }, indent=2))
    print(f"wrote {a.o}")


if __name__ == "__main__":
    main()
