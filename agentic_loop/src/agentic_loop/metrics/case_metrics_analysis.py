import json
from typing import List, Dict, Any

def summarize_case_metrics(case_metrics_list: List[Dict[str, Any]]):
    """Print overall metrics such as CRSR, ISR, FSR and failure-class repairability."""
    n_total = len(case_metrics_list)
    isr = sum(1 for c in case_metrics_list if (c.get("initial_status") or {}).get("tlc")) / n_total if n_total else 0
    fsr = sum(1 for c in case_metrics_list if (c.get("final_status") or {}).get("tlc")) / n_total if n_total else 0
    failing = [c for c in case_metrics_list if not (c.get("initial_status") or {}).get("tlc")]
    n_failing = len(failing)
    crsr = sum(1 for c in failing if (c.get("final_status") or {}).get("tlc")) / n_failing if n_failing else 0
    print(f"Initial TLC Success Rate (ISR): {isr:.2%} ({sum(1 for c in case_metrics_list if (c.get('initial_status') or {}).get('tlc'))}/{n_total})")
    print(f"Final TLC Success Rate (FSR): {fsr:.2%} ({sum(1 for c in case_metrics_list if (c.get('final_status') or {}).get('tlc'))}/{n_total})")
    print(f"Conditional Repair Success Rate (CRSR): {crsr:.2%} ({sum(1 for c in failing if (c.get('final_status') or {}).get('tlc'))}/{n_failing if n_failing else 1})")
    # Failure class repairability table
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
    print("\n| Failure class | Cases | Repaired | Repairability |")
    print("|--------------|-------|----------|--------------|")
    for fc, val in sorted(fc_table.items()):
        total = val["total"]
        repaired = val["repaired"]
        print(f"| {fc} | {total} | {repaired} | {repaired/total:.1%} |")

def summarize_case_metrics_per_mode(baseline_cases, loop_cases):
    """
    Print ISR/FSR/CRSR/failure-class repairability per mode side-by-side.
    """
    # Helper for stats extraction
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
