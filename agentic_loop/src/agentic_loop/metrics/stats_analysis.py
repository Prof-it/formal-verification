import csv
from collections import Counter

def mcnemar_analysis(case_metrics_list, summary_path="mcnemar_summary.txt"):
    mcnemar, binom_test = None, None
    try:
        from statsmodels.stats.contingency_tables import mcnemar
    except ImportError:
        mcnemar = None
    try:
        from scipy.stats import binom_test
    except ImportError:
        binom_test = None
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    def _is_tlc_success(entry):
        tlc_val = (entry.get("final_status") or {}).get("tlc", None)
        if isinstance(tlc_val, bool):
            return tlc_val
        status = (entry.get("TerminalStatus") or entry.get("terminal_status", "") or "")
        return (str(status).lower() == "success")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = _is_tlc_success(base)
        loop_tlc = _is_tlc_success(loop)
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
    if mcnemar is not None:
        table = [[FF, FP], [PF, PP]]
        result = mcnemar(table, exact=True)
        pval = None
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
            import math
            def binom_coeff(n, k):
                return math.comb(n, k)
            b = FP
            c = PF
            discordant = b + c
            if discordant > 0:
                k = min(b, c)
                prob = sum(binom_coeff(discordant, i) * (0.5 ** discordant) for i in range(0, k+1))
                p_conservative = 2 * prob
                lines.append(f"Approximate binomial (no-scipy) p-value: {p_conservative:.3g}\n")
            else:
                lines.append("No discordant pairs: cannot compute binomial p-value.\n")
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
    lines.append(f"Baseline TLC pass rate: {(PF+PP)/n:.1%}\n")
    lines.append(f"Loop TLC pass rate:     {(FP+PP)/n:.1%}\n")
    summary_text = "".join(lines)
    print(summary_text)
    with open(summary_path, "w", encoding="utf-8") as out_f:
        out_f.write(summary_text)
    print(f"\n==> McNemar summary written to {summary_path}")

def mcnemar_markdown(case_metrics_list, md_path="mcnemar_summary.md"):
    # Patch: true pairing
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    def _is_tlc_success(entry):
        tlc_val = (entry.get("final_status") or {}).get("tlc", None)
        if isinstance(tlc_val, bool):
            return tlc_val
        status = (entry.get("TerminalStatus") or entry.get("terminal_status", "") or "")
        return (str(status).lower() == "success")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = _is_tlc_success(base)
        loop_tlc = _is_tlc_success(loop)
        before_after.append((base_tlc, loop_tlc))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]
    PF = counts[(True, False)]
    PP = counts[(True, True)]
    try:
        from statsmodels.stats.contingency_tables import mcnemar as mcnemar_func
        result = mcnemar_func([[FF, FP], [PF, PP]], exact=True)
        pval = result.pvalue
    except Exception:
        pval = None
    table = f"""
|                | After TLC Fail | After TLC Pass |
|:---------------|:--------------|:--------------|
| Before: Fail   | {FF}           | {FP}           |
| Before: Pass   | {PF}           | {PP}           |
"""
    md = (
        "# Paired TLC outcome table (for McNemar's test)\n"
        f"{table}\n"
        f"McNemar p-value: {pval if pval is not None else 'N/A'}\n"
        f"Conditional repair success: {FP}/({FF+FP}) = {(FP/(FF+FP) if (FF+FP)>0 else 0):.1%}\n"
        f"Baseline TLC pass rate: {(PF+PP)/(FF+FP+PF+PP):.1%}\n"
        f"Loop TLC pass rate:     {(FP+PP)/(FF+FP+PF+PP):.1%}\n"
    )
    with open(md_path, "w", encoding="utf-8") as out_f:
        out_f.write(md)
    print(f"McNemar summary written to {md_path}")

def mcnemar_csv(case_metrics_list, csv_path="mcnemar_summary.csv"):
    # Patch: true pairing
    before_after = []
    if len(case_metrics_list) % 2 != 0:
        print("[WARN] case_metrics_list should have even number of entries (baseline/loop pairs)")
    def _is_tlc_success(entry):
        tlc_val = (entry.get("final_status") or {}).get("tlc", None)
        if isinstance(tlc_val, bool):
            return tlc_val
        status = (entry.get("TerminalStatus") or entry.get("terminal_status", "") or "")
        return (str(status).lower() == "success")
    for i in range(0, len(case_metrics_list)-1, 2):
        base = case_metrics_list[i]
        loop = case_metrics_list[i+1]
        base_tlc = _is_tlc_success(base)
        loop_tlc = _is_tlc_success(loop)
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
