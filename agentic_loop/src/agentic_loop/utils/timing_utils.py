import numpy as np

def collect_all_timings(baseline_jsons, loop_jsons):
    all_llm = []
    all_tlc = []
    all_ovh = []
    all_total = []
    all_runs = baseline_jsons + loop_jsons
    for run in all_runs:
        for attempt in run.get("attempts", []):
            timing = attempt.get("timing", {})
            # Only include attempts where timing is present and non-empty
            if timing and "duration_llm" in timing:
                all_llm.append(float(timing.get("duration_llm", 0)))
                all_tlc.append(float(timing.get("duration_tlc", 0)))
                all_ovh.append(float(timing.get("duration_engineering_overhead", 0)))
                all_total.append(float(timing.get("duration_total", 0)))
    return all_llm, all_tlc, all_ovh, all_total

def timing_stats(times):
    if not times:
        return ("—", "—", "—", "—", 0)
    return (
        round(float(np.mean(times)), 2),
        round(float(np.median(times)), 2),
        round(float(np.min(times)), 2),
        round(float(np.max(times)), 2),
        len(times)
    )

def fmt(v, width=5):
    if isinstance(v, (int, float)):
        return f"{v:>{width}.2f}"
    return f"{v:>{width}}"

def fmt_int(v, width=3):
    if isinstance(v, int):
        return f"{v:>{width}d}"
    return f"{v:>{width}}"
