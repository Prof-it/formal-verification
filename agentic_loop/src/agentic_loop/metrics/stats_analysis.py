import csv
import json
import math
import re
from collections import Counter, defaultdict
from statsmodels.stats.contingency_tables import mcnemar
import logging

def trial_id_key(cid):
    """
    Extracts trailing integer from case_id for correct trial sorting.

    - Supports: "trial_2", "baseline_trial_10", "loop_trial_07", etc.
    - If pattern not matched, returns 0 (puts such IDs at the start).
    """
    m = re.search(r'(\d+)$', cid)
    return int(m.group(1)) if m else 0

def _is_tlc_success(entry):
    tlc_val = (entry.get("final_status") or {}).get("tlc", None)
    if isinstance(tlc_val, bool):
        return tlc_val
    status = (entry.get("TerminalStatus") or entry.get("terminal_status", "") or "")
    # Treat both "success" and "skipped" as TLC passes
    return str(status).lower() in ("success", "skipped")

def binom_coeff(n, k):
    return math.comb(n, k)
def mcnemar_analysis(baseline_cases, loop_cases, summary_path="mcnemar_summary.txt"):
    before_after = []
    # Index by case_id for robust matching
    baseline_by_id = {c['case_id']: c for c in baseline_cases}
    loop_by_id = {c['case_id']: c for c in loop_cases}
    common_case_ids = sorted(set(baseline_by_id) & set(loop_by_id), key=trial_id_key)

    for cid in common_case_ids:
        base = baseline_by_id[cid]
        loop = loop_by_id[cid]
        base_tlc = _is_tlc_success(base)
        loop_tlc = _is_tlc_success(loop)
        before_after.append((base_tlc, loop_tlc))
    # (rest is unchanged)

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
        # Try all known ways to get a p-value
        if hasattr(result, "pvalue"):
            pval = getattr(result, "pvalue")
        elif hasattr(result, "__dict__") and "pvalue" in result.__dict__:
            pval = result.__dict__["pvalue"]
        elif isinstance(result, dict) and "pvalue" in result:
            pval = result["pvalue"]
        if pval is not None:
            lines.append(f"McNemar p-value: {pval:.3g}\n")
        else:
            # Manual fallback: binomial p-value calculation for McNemar test (two-tailed) at p=0.5, only standard library.
            b = FP
            c = PF
            discordant = b + c
            if discordant > 0:
                k = min(b, c)
                # Two-sided: sum prob(X <= k) * 2 (for symmetry at p=0.5)
                prob = sum(binom_coeff(discordant, i) * (0.5 ** discordant) for i in range(0, k+1))
                p_conservative = 2 * prob
                lines.append(f"Approximate binomial (no-scipy) p-value: {p_conservative:.3g}\n")
            else:
                lines.append("No discordant pairs: cannot compute binomial p-value.\n")
    else:
        lines.append("Install statsmodels or scipy for p-value.\n")

    # Extra insight
    if n > 0:
        lines.append(f"Baseline TLC pass rate: {(PF+PP)/n:.1%}\n")
        lines.append(f"Loop TLC pass rate:     {(FP+PP)/n:.1%}\n")
    else:
        lines.append("No paired cases for TLC pass rate.\n")


    summary_text = "".join(lines)
    logging.info(summary_text)
    with open(summary_path, "w", encoding="utf-8") as out_f:
        out_f.write(summary_text)
    logging.info(f"\n==> McNemar summary written to {summary_path}")



def mcnemar_markdown(baseline_cases, loop_cases, md_path="mcnemar_summary.md"):

    # Patch: true pairing
    before_after = []
    # Index by case_id for robust matching
    baseline_by_id = {c['case_id']: c for c in baseline_cases}
    loop_by_id = {c['case_id']: c for c in loop_cases}
    common_case_ids = sorted(set(baseline_by_id).intersection(set(loop_by_id)), key=trial_id_key)

    for cid in common_case_ids:
        base = baseline_by_id[cid]
        loop = loop_by_id[cid]
        base_tlc = _is_tlc_success(base)
        loop_tlc = _is_tlc_success(loop)
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
    result = mcnemar([[FF, FP],[PF, PP]], exact=True)
    total = FF + FP + PF + PP
    md = (
        "# Paired TLC outcome table (for McNemar's test)\n"
        f"{table}\n"
        f"McNemar p-value: {result.pvalue:.3g}\n"
        f"Conditional repair success: {FP}/({FF+FP}) = {(FP/(FF+FP) if (FF+FP)>0 else 0):.1%}\n"
    )
    if total > 0:
        md += (
            f"Baseline TLC pass rate: {(PF+PP)/total:.1%}\n"
            f"Loop TLC pass rate:     {(FP+PP)/total:.1%}\n"
        )
    else:
        md += "No paired cases for TLC pass rate.\n"

    with open(md_path, "w", encoding="utf-8") as out_f:
        out_f.write(md)
    logging.info(f"McNemar summary written to {md_path}")

def mcnemar_csv(baseline_cases, loop_cases, csv_path="mcnemar_summary.csv"):
    # Patch: true pairing
    before_after = []
    # Patch: true pairing
    before_after = []
    # Index by case_id for robust matching
    baseline_by_id = {c['case_id']: c for c in baseline_cases}
    loop_by_id = {c['case_id']: c for c in loop_cases}
    common_case_ids = sorted(set(baseline_by_id).intersection(set(loop_by_id)), key=trial_id_key)

    for cid in common_case_ids:
        base = baseline_by_id[cid]
        loop = loop_by_id[cid]
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
    logging.info(f"McNemar table written to {csv_path}")


def reclassify_attempts_with_final_rules(loop_jsons, skills_db, classify_error_func):
    """
    Improved: Prefer skill/rule actually approved and used (if present in skills_applied); otherwise, classify.
    """
    from collections import defaultdict

    counts = defaultdict(lambda: {'occurs': 0, 'fixed': 0, 'ex_rules': set()})
    total_attempts = 0

    for run in loop_jsons:
        attempts = run.get('attempts', [])
        for i, at in enumerate(attempts):
            # Step 1: Prefer recorded skills_applied if available and not empty, and not 'unknown'
            skill_keys = at.get('skills_applied') or []
            if isinstance(skill_keys, str):
                try:
                    skill_keys = json.loads(skill_keys)
                except Exception:
                    skill_keys = [skill_keys]
            skill_class = None
            for k in skill_keys:
                if k != 'unknown':
                    skill_class = k
                    break
            # Step 2: If no skill applied, fallback on classification
            if not skill_class:
                tlc_output = at.get('feedback_excerpt', '') or at.get('status', '')
                skill = classify_error_func(str(tlc_output), skills_db)
                skill_class = skill['key'] if skill and skill.get('key') else 'unknown'
            counts[skill_class]['occurs'] += 1
            total_attempts += 1
            # Log skill as example
            if skill_keys:
                counts[skill_class]['ex_rules'].update(str(r) for r in skill_keys)
            # Success logic: same as before
            next_attempt = attempts[i+1] if i+1 < len(attempts) else None
            if next_attempt and (next_attempt.get('status', '') == 'success'):
                counts[skill_class]['fixed'] += 1
            elif next_attempt:
                # Check if next class is different (use same logic as above)
                n_skill_keys = next_attempt.get('skills_applied') or []
                if isinstance(n_skill_keys, str):
                    try:
                        n_skill_keys = json.loads(n_skill_keys)
                    except Exception:
                        n_skill_keys = [n_skill_keys]
                n_skill_class = None
                for k in n_skill_keys:
                    if k != 'unknown':
                        n_skill_class = k
                        break
                if not n_skill_class:
                    n_tlc_output = next_attempt.get('feedback_excerpt', '') or next_attempt.get('status', '')
                    n_skill = classify_error_func(str(n_tlc_output), skills_db)
                    n_skill_class = n_skill['key'] if n_skill and n_skill.get('key') else 'unknown'
                if n_skill_class != skill_class:
                    counts[skill_class]['fixed'] += 1

    print('\nPer-Attempt (Skill-Aware) Failure Class Repair Stats (Loop mode):')
    print('| Failure Class | Occurrences | Fixed (Repaired/Transitioned) | Success Rate | Example Skill |')
    print('|--------------|-------------|--------------------------|-------------|--------------|')
    for fc, val in sorted(counts.items()):
        occ = val['occurs']
        fixed = val['fixed']
        rate = '{:>5.1f}%'.format(100 * fixed/occ) if occ else '-'
        ex = ', '.join(sorted(val['ex_rules'])) if val['ex_rules'] else '-'
        print(f'| {fc:20s} | {occ:11d} | {fixed:24d} | {rate:10s} | {ex} |')
    print(f'\nTotal repair attempts in loop mode: {total_attempts}')
    return counts


