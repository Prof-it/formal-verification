"""
LLM-prompt and modularity policy utilities for agentic repair loops.
"""

def first_undefined_operator(tlc_output):
    """Extract the first unknown operator mentioned in TLC output."""
    import re
    matches = re.findall(r"Unknown operator: `([^`]+)`", tlc_output)
    return matches[0] if matches else None

def append_single_operator_policy(prompt, first_undefined=None):
    policy = """
IMPORTANT:
- Only propose a repair_skill/rule to address ONE error/root cause at a time (normally, ONE undefined/missing operator, e.g., 'Subset', 'Sum', etc).
- If multiple undefined operators/errors are present in TLC output, address ONLY the FIRST one (use order of appearance, or if specified in context).
- If your previous response was rejected for being non-modular, ONLY propose a fix for just ONE (the first) this turn.
Do NOT propose fixes or definitions for more than one operator/root cause at a time.
"""
    if first_undefined:
        policy += f"\nFirst undefined operator to address: {first_undefined}"
    return prompt + "\n" + policy