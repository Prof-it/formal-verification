"""General helper utilities for agentic_loop."""

import re


def print_source_with_line_numbers(filepath):
    """
    Print the content of a file with line numbers to standard out.
    """
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            lines = f.readlines()
        print("\n----- Current TLA+ Spec (with line numbers) -----")
        for idx, line in enumerate(lines, 1):
            print(f"{idx:4}: {line.rstrip()}")
        print("-------------------------------------------------\n")
    except Exception as e:
        print(f"[WARN] Could not display source file {filepath}: {e}")

def is_multi_operator_issue(candidate_rule, repair_skill_text):
    """
    Returns True if candidate_rule or repair_skill_text mention >1 unknown operator/root cause in a single fix.
    Typical patterns: Unknown operator: Subset, Sum; or plan text says fix Subset and Sum, etc.
    """
    if candidate_rule and "pattern" in candidate_rule:
        # If pattern lists multiple operators (comma, |, or and-based logic)
        pat = candidate_rule["pattern"]
        # Count how many operator-like-words by splitting on backticks (`)
        ops = [x for x in re.findall(r"`([^`]+)`", pat)]
        # Multi if >1 operator mentioned
        if len(ops) > 1:
            return True
        # Textual separator check
        if re.search(r",| and |\\|", pat):
            return True
    if repair_skill_text:
        # Look for explicit requests to define multiple operators, or multiple "Unknown operator" phrases
        multi_op_refs = len(re.findall(r"Unknown operator: ", repair_skill_text)) > 1
        ands = re.search(r"define.* and .* operator", repair_skill_text, re.IGNORECASE)
        comma = "," in repair_skill_text and "operator" in repair_skill_text
        pipes = "|" in repair_skill_text and "operator" in repair_skill_text
        if multi_op_refs or ands or comma or pipes:
            return True
    return False
