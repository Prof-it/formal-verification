import csv
import argparse

def parse_args():
    parser = argparse.ArgumentParser(description="Print TLC Success Cascade Table from case_metrics file")
    parser.add_argument("--case-metrics", required=True, help="Path to the case_metrics.csv file")
    return parser.parse_args()

def load_case_metrics_csv(path):
    """
    Returns: (baseline_list, loop_list) - each is a list of dicts
    Assumes file alternates: baseline, loop, baseline, loop...
    """
    baseline, loop = [], []
    with open(path, newline='', encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
        for i, row in enumerate(rows):
            if 'mode' in row and row['mode'].lower().startswith("baseline"):
                baseline.append(row)
            elif 'mode' in row and row['mode'].lower().startswith("loop"):
                loop.append(row)
            else:
                # fallback: alternate
                (baseline if (i%2==0) else loop).append(row)
    assert len(baseline) == len(loop), "Mismatched number of baseline and loop rows!"
    return baseline, loop

def get_tlc_pass(casedict, field="final_status"):
    """
    Flexible extractor for boolean TLC pass from serialized dict or string
    Assumes the field 'final_status' is a JSON string or dict with key 'tlc'
    """
    import json
    status = casedict.get(field, "")
    if isinstance(status, dict):
        return bool(status.get("tlc", False))
    try:
        return bool(json.loads(status).get("tlc", False))
    except Exception:
        return False

def print_tlc_success_cascade_table_csv(baseline_list, loop_list):
    """
    Print cascade table using data loaded from case_metrics.csv
    """
    cascade_counts = {"A": 0, "B": 0, "C": 0, "D": 0}
    total = len(baseline_list)
    for b, l in zip(baseline_list, loop_list):
        b_pass = get_tlc_pass(b)
        l_pass = get_tlc_pass(l)
        if b_pass and l_pass:
            cascade_counts["A"] += 1
        elif b_pass and not l_pass:
            cascade_counts["B"] += 1
        elif not b_pass and l_pass:
            cascade_counts["C"] += 1
        elif not b_pass and not l_pass:
            cascade_counts["D"] += 1

    A,B,C,D = [cascade_counts[k] for k in "ABCD"]
    print("== TLC Success Cascade Table ==")
    print(f"|                | Loop Pass | Loop Fail | Total    |")
    print(f"|----------------|-----------|-----------|----------|")
    print(f"| Baseline Pass  |{A:^11d}|{B:^11d}|{A+B:^10d}|")
    print(f"| Baseline Fail  |{C:^11d}|{D:^11d}|{C+D:^10d}|")
    print(f"| Total          |{A+C:^11d}|{B+D:^11d}|{total:^10d}|")
    print()
    # Key stats
    print(f"- Baseline TLC pass rate:   {(A+B)/total:.1%} ({A+B}/{total})")
    print(f"- Loop TLC pass rate:       {(A+C)/total:.1%} ({A+C}/{total})")
    print(f"- Conditional repair (loop fixes baseline fails): " +
          (f"{C}/({C+D}) = {(C/(C+D))*100:.1f}%" if (C+D) else "-"))
    print(f"- Regression rate (loop fails where baseline passes): " +
          (f"{B}/({A+B}) = {(B/(A+B))*100:.1f}%" if (A+B) else "-"))
    print(f"- Raw lift (added loop successes minus regressions): " +
          (f"({C}-{B})/{total} = {(C-B)/total*100:.1f}%" if total else "-"))
    print(f"- Trials with at least one pass: {A+B+C}/{total} = {(A+B+C)/total:.1%}")
    print(f"- Trials where both failed: {D}/{total} = {(D/total):.1%}")
    print()
    print("Legend: A: both pass, B: regression, C: fixed by loop, D: both fail")

def main():
    args = parse_args()
    baseline_list, loop_list = load_case_metrics_csv(args.case_metrics)
    print_tlc_success_cascade_table_csv(baseline_list, loop_list)

if __name__ == "__main__":
    main()
