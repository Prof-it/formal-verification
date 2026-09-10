import os
import json
import csv
import numpy as np
from pathlib import Path
from collections import Counter
import sys

try:
    from statsmodels.stats.contingency_tables import mcnemar
except ImportError:
    mcnemar = None
try:
    from scipy.stats import binom_test
except ImportError:
    binom_test = None


import argparse

def parse_args():
    parser = argparse.ArgumentParser(description="Analyze agentic loop verification experiments")
    parser.add_argument('results_root', help="Directory with output folders (baseline, loop, ...)")
    parser.add_argument('--num-trials', type=int, default=100, help='Number of trials')
    parser.add_argument('--result-name', default='nasa_ddmr26_run.json', help='Per-trial filename') # In case you want to tweak
    return parser.parse_args()



def _write_case_metrics_csv(csv_path, case_metrics_list):
    """Copied from compare_cli.py"""
    keys = [
        "case_id", "mode", "initial_candidate", "initial_status", "final_status",
        "repair_attempts", "repair_success",
        "initial_failure_classes", "resolved_failure_classes", "remaining_failure_classes", "artifact_dir"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        for cm in case_metrics_list:
            row = cm.copy()
            for k, v in row.items():
                if isinstance(v, (dict, list)):
                    row[k] = json.dumps(v)
            writer.writerow(row)


def mcnemar_analysis(case_metrics_list, summary_path="mcnemar_summary.txt"):
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = bool((base.get("final_status") or {}).get("tlc", False))
        loop_tlc = bool((loop.get("final_status") or {}).get("tlc", False))
        before_after.append((base_tlc, loop_tlc))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]   # Baseline fail, Loop pass: repaired!
    PF = counts[(True, False)]   # Baseline pass, Loop fail: regression (should be 0)
    PP = counts[(True, True)]
    n = FF + FP + PF + PP

    lines = []
    lines.append("\nPaired TLC outcomes:\n")
    lines.append("Initial TLC  | After TLC Fail | After TLC Pass |\n")
    lines.append("-------------|----------------|---------------|\n")
    lines.append(f"Fail         |   {FF:<14d}| {FP:<14d}|\n")
    lines.append(f"Pass         |   {PF:<14d}| {PP:<14d}|\n")

    lines.append(f"\nMcNemar's test on discordant pairs (Baseline fail→Loop pass={FP}, Baseline pass→Loop fail={PF})\n")
    pval = None
    if mcnemar is not None:
        table = [[FF, FP], [PF, PP]]
        result = mcnemar(table, exact=True)
        if hasattr(result, "pvalue"):
            pval = getattr(result, "pvalue")
        elif hasattr(result, "__dict__") and "pvalue" in result.__dict__:
            pval = result.__dict__["pvalue"]
        elif isinstance(result, dict) and "pvalue" in result:
            pval = result["pvalue"]
        if pval is not None:
            lines.append(f"McNemar p-value: {pval:.3g}\n")
    elif binom_test is not None:
        b = FP
        c = PF
        discordant = b + c
        if discordant > 0:
            p = 2 * binom_test(min(b, c), n=discordant, p=0.5, alternative='two-sided')
            lines.append(f"Binomial p-value (McNemar fallback): {p:.3g}\n")
        else:
            lines.append("Binomial test not applicable (no discordant pairs).\n")
    else:
        lines.append("Install statsmodels or scipy for p-value.\n")
    lines.append(f"Baseline TLC pass rate: {(PF+PP)/n if n else 0:.1%}\n")
    lines.append(f"Loop TLC pass rate:     {(FP+PP)/n if n else 0:.1%}\n")
    summary_text = "".join(lines)
    print(summary_text)
    with open(summary_path, "w", encoding="utf-8") as out_f:
        out_f.write(summary_text)
    print(f"\n==> McNemar summary written to {summary_path}")

def mcnemar_markdown(case_metrics_list, md_path="mcnemar_summary.md"):
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = bool((base.get("final_status") or {}).get("tlc", False))
        loop_tlc = bool((loop.get("final_status") or {}).get("tlc", False))
        before_after.append((base_tlc, loop_tlc))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]
    PF = counts[(True, False)]
    PP = counts[(True, True)]
    table = f"""
|                | After TLC Fail | After TLC Pass |
|:---------------|:--------------|:--------------|
| Before: Fail   | {FF}           | {FP}           |
| Before: Pass   | {PF}           | {PP}           |
"""
    # Use McNemar if available for p-value
    result = None
    pval = None
    if mcnemar is not None:
        result = mcnemar([[FF, FP],[PF, PP]], exact=True)
        pval = getattr(result, "pvalue", None)
    md = (
        "# Paired TLC outcome table (for McNemar's test)\n"
        f"{table}\n"
        f"McNemar p-value: {pval if pval is not None else 'NA'}\n"
        f"Conditional repair success: {FP}/({FF+FP}) = {(FP/(FF+FP) if (FF+FP)>0 else 0):.1%}\n"
        f"Baseline TLC pass rate: {(PF+PP)/(FF+FP+PF+PP):.1%}\n"
        f"Loop TLC pass rate:     {(FP+PP)/(FF+FP+PF+PP):.1%}\n"
    )
    with open(md_path, "w", encoding="utf-8") as out_f:
        out_f.write(md)
    print(f"McNemar summary written to {md_path}")

def mcnemar_csv(case_metrics_list, csv_path="mcnemar_summary.csv"):
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = bool((base.get("final_status") or {}).get("tlc", False))
        loop_tlc = bool((loop.get("final_status") or {}).get("tlc", False))
        before_after.append((base_tlc, loop_tlc))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]
    PF = counts[(True, False)]
    PP = counts[(True, True)]
    with open(csv_path, "w", newline='', encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["", "After TLC Fail", "After TLC Pass"])
        writer.writerow(["Before: Fail", FF, FP])
        writer.writerow(["Before: Pass", PF, PP])
    print(f"McNemar table written to {csv_path}")

def collect_all_timings(baseline_jsons, loop_jsons):
    all_llm = []
    all_tlc = []
    all_ovh = []
    all_total = []
    all_runs = baseline_jsons + loop_jsons
    for run in all_runs:
        for attempt in run.get("attempts", []):
            timing = attempt.get("timing", {})
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

def summarize_case_metrics_per_mode(baseline_cases, loop_cases):
    import json
    def extract_stats(cases):
        n_total = len(cases)
        isr = sum(1 for c in cases if (c.get("initial_status") or {}).get("tlc")) / n_total if n_total else 0
        fsr = sum(1 for c in cases if (c.get("final_status") or {}).get("tlc")) / n_total if n_total else 0
        failing = [c for c in cases if not (c.get("initial_status") or {}).get("tlc")]
        n_failing = len(failing)
        crsr = sum(1 for c in failing if (c.get("final_status") or {}).get("tlc")) / n_failing if n_failing else 0
        return dict(ISR=isr, FSR=fsr, CRSR=crsr, n_total=n_total, n_failing=n_failing)
    b_stats = extract_stats(baseline_cases)
    l_stats = extract_stats(loop_cases)
    print("\nSuccess Rate Comparison (per mode):")
    print("| Metric | Baseline | Loop |")
    print("|--------|----------|------|")
    print(f"| ISR    | {b_stats['ISR']:.2%} ({sum(1 for c in baseline_cases if (c.get('initial_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['ISR']:.2%} ({sum(1 for c in loop_cases if (c.get('initial_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    print(f"| FSR    | {b_stats['FSR']:.2%} ({sum(1 for c in baseline_cases if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['FSR']:.2%} ({sum(1 for c in loop_cases if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    print(f"| CRSR   | {b_stats['CRSR']:.2%} ({sum(1 for c in [c for c in baseline_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_failing'] if b_stats['n_failing'] else 1}) | "
          f"{l_stats['CRSR']:.2%} ({sum(1 for c in [c for c in loop_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_failing'] if l_stats['n_failing'] else 1}) |")

    def failure_class_table(cases, label):
        failing = [c for c in cases if not (c.get("initial_status") or {}).get("tlc")]
        fc_table = {}
        for case in failing:
            fclist = case.get("initial_failure_classes", [])
            if isinstance(fclist, str):
                try:
                    fclist = json.loads(fclist)
                except Exception:
                    fclist = []
            for fc in fclist:
                if fc not in fc_table:
                    fc_table[fc] = {"total": 0, "repaired": 0}
                fc_table[fc]["total"] += 1
                if (case.get("final_status") or {}).get("tlc"):
                    fc_table[fc]["repaired"] += 1
        print(f"\n| Failure class ({label}) | Cases | Repaired | Repairability |")
        print("|----------------------|-------|----------|--------------|")
        for fc, val in sorted(fc_table.items()):
            total = val["total"]
            repaired = val["repaired"]
            rep_rate = (repaired/total)*100 if total > 0 else 0
            print(f"| {fc} | {total} | {repaired} | {rep_rate:.1f}% |")
    failure_class_table(baseline_cases, "baseline")
    failure_class_table(loop_cases, "loop")

def main():
    args = parse_args()
    results_root = args.results_root
    NUM_TRIALS = args.num_trials
    result_name = args.result_name
    print(f"Analyzing results in {results_root}, num_trials = {NUM_TRIALS}")

    baseline_jsons = []
    loop_jsons = []
    baseline_cases = []
    loop_cases = []
    all_case_metrics = []
    trial_pairs = []      # List of (trial_idx, baseline_case, loop_case)

    for i in range(1, NUM_TRIALS+1):
        base_path = Path(results_root) / "baseline" / f"trial_{i:02d}" / result_name
        loop_path = Path(results_root) / "loop" / f"trial_{i:02d}" / result_name
        if not (base_path.exists() and loop_path.exists()):
            print(f"[WARN] Missing trial {i:02d}: {base_path} {loop_path}")
            continue
        with open(base_path, "r") as f:
            b = json.load(f)
        with open(loop_path, "r") as f:
            l = json.load(f)

        # Build entries as compare_cli.py
        b_case_metrics = b.get("case_metrics", {})
        l_case_metrics = l.get("case_metrics", {})

        baseline_jsons.append(b)   
        loop_jsons.append(l)       

        entry_b = {
            "mode": "baseline",
            "initial_status": {"tlc": bool(
                b.get("InitialVerificationSuccess", b.get("initial_verification_success", False))
            )},
            "final_status": {"tlc": bool(
                b.get("TerminalStatus", b.get("terminal_status", "")) == "success"
            )},
            "initial_failure_classes": b_case_metrics.get("initial_failure_classes", [])
        }
        entry_l = {
            "mode": "loop",
            "initial_status": {"tlc": bool(
                l.get("InitialVerificationSuccess", l.get("initial_verification_success", False))
            )},
            "final_status": {"tlc": bool(
                l.get("TerminalStatus", l.get("terminal_status", "")) == "success"
            )},
            "initial_failure_classes": l_case_metrics.get("initial_failure_classes", [])
        }
        trial_pairs.append((i, entry_b, entry_l))

        # Full per-case-metrics, for csv etc.
        if b_case_metrics:
            row = b_case_metrics.copy()
            row["mode"] = "baseline"
            all_case_metrics.append(row)
        if l_case_metrics:
            row = l_case_metrics.copy()
            row["mode"] = "loop"
            all_case_metrics.append(row)

    # Now—reliably paired
    paired_case_metrics = []
    baseline_cases = []
    loop_cases = []
    for trial_idx, b_entry, l_entry in trial_pairs:
        paired_case_metrics.append(b_entry)
        paired_case_metrics.append(l_entry)
        baseline_cases.append(b_entry)
        loop_cases.append(l_entry)



    # Write case metrics CSV as before
    csv_path = Path(results_root) / "case_metrics.csv"
    _write_case_metrics_csv(csv_path, all_case_metrics)
    print(f"\nWrote detailed case metrics CSV: {csv_path}")

    # -- STRICT PAIRED LOGIC: Interleave baseline/loop entries for each trial --
    paired_case_metrics = []
    for i in range(len(baseline_cases)):
        b_entry = baseline_cases[i]
        l_entry = loop_cases[i]
        paired_case_metrics.append(b_entry)
        paired_case_metrics.append(l_entry)
        # For debugging, print TRUE regressions
        def _is_tlc_success(entry):
            tlc_val = (entry.get("final_status") or {}).get("tlc", None)
            if isinstance(tlc_val, bool):
                return tlc_val
            status = (entry.get("TerminalStatus") or entry.get("terminal_status", "") or "")
            return (str(status).lower() == "success")
        if _is_tlc_success(b_entry) and not _is_tlc_success(l_entry):
            print(f"REGRESSION: trial {i+1:02d} baseline=success, loop={l_entry.get('final_status')}")


    # Use paired_case_metrics for all outcome analysis! (now matches compare_cli.py logic)
    mcnemar_analysis(paired_case_metrics, summary_path=str(Path(results_root) / "mcnemar_summary.txt"))
    mcnemar_markdown(paired_case_metrics, md_path=str(Path(results_root) / "mcnemar_summary.md"))
    mcnemar_csv(paired_case_metrics, csv_path=str(Path(results_root) / "mcnemar_summary.csv"))

    # For per-mode stats, keep using baseline_cases and loop_cases
    summarize_case_metrics_per_mode(baseline_cases, loop_cases)

    # Timing stats
    all_llm, all_tlc, all_ovh, all_total = collect_all_timings(baseline_jsons, loop_jsons)
    print("\nTiming statistics per phase (seconds):")
    phases = [
        ("LLM call", all_llm),
        ("TLC call", all_tlc),
        ("Engineering overhead", all_ovh),
        ("Total step", all_total)
    ]
    print("| Phase                | Mean | Median | Min | Max | Attempts |")
    print("|--------------------- |------|--------|-----|-----|----------|")
    for label, data in phases:
        mean_, median_, min_, max_, N_ = timing_stats(data)
        print(f"| {label:<20} | {fmt(mean_)} | {fmt(median_,6)} | {fmt(min_,3)} | {fmt(max_,3)} | {fmt_int(N_,3)} |")

if __name__ == "__main__":
    main()
