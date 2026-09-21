import json
import re

_SKILL_ATTEMPTS_SESS = set()

def validate_skill_recursion(repair_skill_text, fn_name):
    # Checks if a recursive definition for fn_name is missing RECURSIVE declaration.
    if fn_name in repair_skill_text and "RECURSIVE" not in repair_skill_text:
        return False
    return True

def has_skill_been_applied(error_key, skill_key):
    return (error_key, skill_key) in _SKILL_ATTEMPTS_SESS

def register_skill_applied(error_key, skill_key):
    _SKILL_ATTEMPTS_SESS.add((error_key, skill_key))

def clear_skill_attempt_session():
    _SKILL_ATTEMPTS_SESS.clear()

def get_recursively_defined_functions(tla_code: str):
    """
    Returns a set of function/operator names in TLA+ code that are recursively self-referential,
    but are missing a corresponding RECURSIVE declaration.
    """
    # Find all operator definitions Foo(...) ==
    operator_defs = re.findall(r'^([A-Za-z_][A-Za-z0-9_]*)\\s*\\(.*?\\)\\s*==', tla_code, flags=re.MULTILINE)
    missing_recursive = set()
    for name in operator_defs:
        # Is the operator used recursively inside its own body?
        pattern = rf'^{name}\s*\(.*?\)\s*==((?:.|\n)*?)(?=^[A-Za-z_][A-Za-z0-9_]*\s*\(.*?\)\s*==|^$|^====)'
        match = re.search(pattern, tla_code, flags=re.MULTILINE)
        if match:
            body = match.group(1)
            # Self-referential call within body (exclude the function signature line)
            found_recursive = re.search(rf'(?<!RECURSIVE\s){name}\s*\(', body)
            if found_recursive:
                # Check for corresponding RECURSIVE statement
                rec_decl = re.search(rf'RECURSIVE\s+{name}\s*\(', tla_code)
                if not rec_decl:
                    missing_recursive.add(name)
    return missing_recursive

def attempt_register_skill(candidate_rule):
    """
    Register skill only if it has not been applied to the same error already.
    Returns True if skill can be persisted/applied, False if deadlock detected.
    """
    error_key = candidate_rule.get("key")
    skill_key = candidate_rule.get("key")
    if has_skill_been_applied(error_key, skill_key):
        print(f"\n[Agentic Loop Deadlock] The rule '{skill_key}' for error '{error_key}' was applied already with no progress.")
        print("This suggests the rule is incorrect or incomplete. Please review/correct or create a new fix, then approve.")
        return False
    register_skill_applied(error_key, skill_key)
    return True

def try_register_candidate_rule(candidate_rule, skills_db, pending_session_rule=None):
    """
    Idempotently register candidate_rule into skills_db unless it's been tried for this error before.
    - Returns (True, new_pending_session_rule) if registered (or not a deadlock).
    - Returns (False, _) and handles messaging if deadlock detected (caller should break loop).
    """
    error_key = candidate_rule.get('key')
    skill_key = candidate_rule.get('key')
    if has_skill_been_applied(error_key, skill_key):
        print(f"\n[Agentic Loop Deadlock] The rule '{skill_key}' for error '{error_key}' was applied already with no progress.")
        print("This suggests the rule is incorrect or incomplete. Please review/correct or create a new fix, then approve.")
        return False, pending_session_rule
    register_skill_applied(error_key, skill_key)
    # ---- FIX: ensure all required fields ----
    if 'strategy' not in candidate_rule:
        candidate_rule['strategy'] = candidate_rule.get('suggested_skill') or \
            f"human approved repair for {candidate_rule.get('key','unknown')}"
    if 'suggested_skill' not in candidate_rule:
        candidate_rule['suggested_skill'] = candidate_rule.get('strategy', '')
    skills_db.append(candidate_rule)
    pending_session_rule = candidate_rule
    return True, pending_session_rule

def apply_known_skill(spec_text, skill):
    """
    Apply the concrete or templated skill as a patch to the TLA+ code.
    Supports replacement of placeholders like {fn} if available, but works with static skills too.
    """
    code = skill.get("suggested_skill") or skill.get("strategy", "")
    groups = skill.get("groups", {})  # For named regex groups (if any)
    match_str = skill.get("match", "")
    fn = None
    # Try to fill placeholders if present and available
    # Search for a generic placeholder {fn}, or more custom ones as needed
    if "{fn}" in code:
        # Look for named group 'fn'
        if "fn" in groups:
            fn = groups["fn"]
        elif groups:
            # Try first group
            fn = next(iter(groups.values()))
        else:
            # fallback: parse from match string for common pattern
            m = re.search(r"Unknown operator: [`']?([A-Za-z_][A-Za-z0-9_]*)[`']?", match_str)
            if m:
                fn = m.group(1)
        if fn:
            code = code.replace("{fn}", fn)
    # Prepare code block (strip markdown, get only TLA+ lines)
    code_lines = []
    in_code = False
    for line in code.splitlines():
        if line.strip().startswith("```"):
            in_code = not in_code
            continue
        # Heuristic: keep likely code lines
        if in_code or (re.match(r'^[A-Za-z_][A-Za-z0-9_ ]*==', line.strip()) or "==" in line or "[" in line):
            code_lines.append(line.rstrip())
    block = "\n".join(code_lines) if code_lines else code
    # Optionally, for operator skills, remove old definitions if fn is found
    if fn:
        # catch both (args) and [domain] forms
        pattern = re.compile(rf"^{fn}\s*(\([^\)]*\)|\[[^\]]*\])\s*==.*?(?=^[A-Za-z_][A-Za-z0-9_]*\s*(\([^\)]*\)|\[[^\]]*\])\s*==|^====$)", flags=re.MULTILINE|re.DOTALL)
        spec_text = re.sub(pattern, '', spec_text)
    # Insert before final ==== separator if possible
    idx = spec_text.rfind("=" * 4)
    if idx != -1:
        pre = spec_text[:idx].rstrip()
        post = spec_text[idx:]
        new_spec = pre + "\n" + block.strip() + "\n" + post
        return new_spec
    else:
        # Fallback: just append
        return spec_text.rstrip() + "\n" + block.strip() + "\n"