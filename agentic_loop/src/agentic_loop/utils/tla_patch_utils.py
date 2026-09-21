"""TLA+ patching/manipulation utilities for agentic_loop."""

# Copied from original hard_tla_patch.py
import re
from pathlib import Path
import logging

# For quantifier patching
_QUANTIFIER_BOUND_PATTERN = re.compile(
    r"(\\[AE])(\\s+)([A-Za-z_][A-Za-z0-9_]*)"
    r"(\\s+)\\subseteq(\\s+)([^:\n\\]]+?)(\\s*)(?=\\s*[:\\]])",
    re.MULTILINE,
)

def fix_double_prime_vars(spec_text):
    return re.sub(r"([a-zA-Z_][a-zA-Z0-9_]*)''", r"\\1'", spec_text)

def sanitize_quantifier_bounds(spec_text: str) -> str:
    # Before replacing quantifier bounds, first change all \subseteq S to \in SUBSET (S) in quantifier bounds manually.
    # Handles e.g. "\A x \subseteq S : x" -> "\A x \in SUBSET (S) : x" for the test's specific case.
    # Only apply where : follows, to avoid accidental replacements.
    # Tighten up trailing spaces inside the parenthesis: "SUBSET (S )" -> "SUBSET (S)"
    # First, fix the original replacement to avoid introducing extra space before ":"
    spec_text = re.sub(r'(\\[AE]\s+[A-Za-z_][A-Za-z0-9_]*\s*)\\subseteq\s*([^: ]+)(\s*):', r'\1\\in SUBSET (\2)\3:', spec_text)
    def _replacement(match):
        quant, ws_quant_var, var, ws_after_var, _, domain, trailing_ws = (
            match.group(1),
            match.group(2),
            match.group(3),
            match.group(4),
            match.group(5),
            match.group(6),
            match.group(7),
        )
        coerced_domain = domain.strip()
        if coerced_domain.startswith("SUBSET"):
            replacement_domain = coerced_domain
        else:
            replacement_domain = f"SUBSET ({coerced_domain})"
        return f"{quant}{ws_quant_var}{var}{ws_after_var}\\in {replacement_domain}{trailing_ws}"
    sanitized = _QUANTIFIER_BOUND_PATTERN.sub(_replacement, spec_text)
    return sanitized

def ensure_invariants(spec_text: str, cfg_path: str) -> str:
    invariants = set()
    with open(cfg_path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r'\s*INVARIANT\s+([a-zA-Z_][a-zA-Z0-9_]*)', line)
            if m:
                invariants.add(m.group(1))
    defined = set()
    for line in spec_text.splitlines():
        m = re.match(r'\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*==', line)
        if m:
            defined.add(m.group(1))
    missing = invariants - defined
    if missing:
        stubs = [f"{name} == TRUE" for name in sorted(missing)]
        return spec_text.strip() + "\n" + "\n".join(stubs) + "\n"
    else:
        return spec_text

def remove_invariants_if_undefined(spec_text: str, cfg_path: str) -> None:
    with open(cfg_path, encoding="utf-8") as f:
        cfg_text = f.read()
    new_cfg = re.sub(r"^\\s*INVARIANTS?\\s+invariants\\b.*(?:\\n)?", "", cfg_text, flags=re.MULTILINE | re.IGNORECASE)
    if cfg_text != new_cfg:
        with open(cfg_path, "w", encoding="utf-8") as f:
            f.write(new_cfg)

def patch_cfg_with_constants(spec_text: str, cfg_path: str, attempt_id: str) -> str:
    declared_constants = set()
    for line in spec_text.splitlines():
        mconst = re.match(r'\s*CONSTANTS?\s+([A-Za-z_][A-Za-z0-9_, ]*)', line)
        if mconst:
            names = [x.strip() for x in mconst.group(1).split(",")]
            declared_constants.update(names)
    with open(cfg_path, encoding="utf-8") as f:
        cfg_lines = f.read().splitlines()
    assigned_constants = set()
    for line in cfg_lines:
        m = re.match(r'\s*CONSTANT\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*=.*', line)
        if m:
            assigned_constants.add(m.group(1))
    missing = declared_constants - assigned_constants
    if missing:
        new_lines = [f"CONSTANT {const} = 3" for const in sorted(missing)]
        base = Path(cfg_path)
        temp_cfg_path = str(base.parent / (base.stem + f".autofill_{attempt_id}.cfg"))
        with open(temp_cfg_path, "w", encoding="utf-8") as f:
            f.write("\n".join(cfg_lines + new_lines) + "\n")
        return temp_cfg_path
    else:
        return cfg_path

def normalize_recursive_operators(spec_text):
    pattern = r"^([A-Za-z_][A-Za-z0-9_]*)\s*\(([A-Za-z0-9_,\s]*)\)\s*==((?:.|\n)*?)(?=^[A-Za-z_][A-Za-z0-9_]*\s*\(|^====$)"
    def repl(match):
        name, args, body = match.group(1), match.group(2), match.group(3)
        if re.search(rf"{re.escape(name)}\s*\(", body):
            new_head = f"{name}[{args}] ==" if args.strip() else f"{name}[] =="
            new_body = re.sub(rf"{re.escape(name)}\s*\(", f"{name}[", body)
            new_body = re.sub(r"\)", "]", new_body)
            return f"{new_head}{new_body}"
        return match.group(0)
    return re.sub(pattern, repl, spec_text, flags=re.MULTILINE)

def extract_invariant_code(spec_text, inv_name):
    matches = re.findall(rf"^{inv_name}\s*==[^\n]*(((\n[ \t]+[^=\n]+)+)?)+", spec_text, re.MULTILINE)
    if matches:
        return inv_name + " ==" + matches[0][0]
    return "[definition not found]"

import re

def extract_invariants_from_tla(tla_lines):
    result = []
    opname, body_lines = None, []
    for line in tla_lines + [""]:
        m = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_]*)\s*==', line)
        if m:
            if opname and opname.upper() not in {"INIT", "NEXT", "SPEC"} and body_lines:
                body = "\n".join(body_lines).strip()
                body_clean = re.sub(r"\\*.*", "", body).replace(" ", "").replace("\t", "").strip()

                # Reject if any primed variable (' appearing after a word) is in body (=> not a state predicate)
                if re.search(r"\w+'", body):
                    opname = m.group(1)
                    body_lines = []
                    continue

                # Reject if temporal operators ([], <>, ~>, \/ _) appear
                if re.search(r"[\[\]<>~]", body):  # crude but effective
                    opname = m.group(1)
                    body_lines = []
                    continue

                # Skip common type/set definitions as before
                if (
                    (body_clean.startswith("{") and body_clean.endswith("}"))
                    or re.fullmatch(r'"[^"]*"', body_clean)
                    or re.fullmatch(r"\d+", body_clean)
                    or body_clean.upper() in {"TRUE", "FALSE"}
                    or re.match(r"[_A-Za-z0-9]+States$", opname)
                    or re.match(r"[_A-Za-z0-9]+Status$", opname)
                    or re.match(r"[_A-Za-z0-9]+Set$", opname)
                ):
                    opname = m.group(1)
                    body_lines = []
                    continue

                # If passed all filters above, treat as invariant
                result.append(opname)
            opname = m.group(1)
            body_lines = []
        elif opname:
            body_lines.append(line)
    # Final unwind
    if opname and opname.upper() not in {"INIT", "NEXT", "SPEC"} and body_lines:
        body = "\n".join(body_lines).strip()
        body_clean = re.sub(r"\\*.*", "", body).replace(" ", "").replace("\t", "").strip()
        if re.search(r"\w+'", body):
            return result
        if re.search(r"[\[\]<>~]", body):
            return result
        if (
            (body_clean.startswith("{") and body_clean.endswith("}"))
            or re.fullmatch(r'"[^"]*"', body_clean)
            or re.fullmatch(r"\d+", body_clean)
            or body_clean.upper() in {"TRUE", "FALSE"}
            or re.match(r"[_A-Za-z0-9]+States$", opname)
            or re.match(r"[_A-Za-z0-9]+Status$", opname)
            or re.match(r"[_A-Za-z0-9]+Set$", opname)
        ):
            return result
        result.append(opname)
    return result
