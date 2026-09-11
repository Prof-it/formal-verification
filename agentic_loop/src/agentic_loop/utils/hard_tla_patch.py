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
    replacements = 0
    def _replacement(match):
        # ... (same replacement logic as before) ...
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
    """
    Ensure all invariants listed in cfg are present in the TLA+ spec, adding TRUE stubs if missing.
    """
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
    """
    Remove literal dummy invariants entry from cfg if present.
    """
    with open(cfg_path, encoding="utf-8") as f:
        cfg_text = f.read()
    new_cfg = re.sub(r"^\\s*INVARIANTS?\\s+invariants\\b.*(?:\\n)?", "", cfg_text, flags=re.MULTILINE | re.IGNORECASE)
    if cfg_text != new_cfg:
        with open(cfg_path, "w", encoding="utf-8") as f:
            f.write(new_cfg)

def patch_cfg_with_constants(spec_text: str, cfg_path: str, attempt_id: str) -> str:
    """
    Ensure all constants declared in the TLA+ spec are assigned in the .cfg, with defaults if missing.
    """
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
    """
    Converts recursive operators defined with parentheses/calls
    to TLA+ function bracket-domain style. E.g.:
    Foo(x) == ... Foo(y) ...  -->  Foo[x] == ... Foo[y] ...
    Does NOT guess or fill domains; manual review suggested.
    """
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



def extract_invariants_from_tla(tla_lines):
    result = []
    opname, body_lines = None, []
    for line in tla_lines + [""]:
        m = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_]*)\s*==', line)
        if m:
            # flush previously captured operator
            if opname and opname.upper() not in {"INIT", "NEXT", "SPEC"} and body_lines:
                body = "\n".join(body_lines).strip()
                if not re.search(r"\w+'", body):
                    result.append(opname)
            opname = m.group(1)
            body_lines = []
        elif opname:
            body_lines.append(line)
    if opname and opname.upper() not in {"INIT", "NEXT", "SPEC"} and body_lines:
        body = "\n".join(body_lines).strip()
        if not re.search(r"\w+'", body):
            result.append(opname)
    return result
