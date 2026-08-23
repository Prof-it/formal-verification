from __future__ import annotations

from dataclasses import dataclass
from logging import config
from pathlib import Path
from typing import Callable, Dict, Optional
from unittest import result

from .models import AttemptRecord, LoopConfig, RunResult, TaskSpec
from .prompting import load_prompt_template, render_prompt
from .providers import LLMProvider
from .reporting import persist_run_result
from .tlc_runner import run_tlc

import json
import shutil
import warnings
import time
import os
import shutil as _shutil
import re
import random
import numpy as np

@dataclass(frozen=True)
class PurgeStats:
    removed_directories: int = 0
    reclaimed_bytes: int = 0

    def as_log_message(self) -> str:
        size = self.reclaimed_bytes
        units = ["B", "KiB", "MiB", "GiB"]
        unit_index = 0
        while size >= 1024 and unit_index < len(units) - 1:
            size /= 1024.0
            unit_index += 1
        size_str = f"{size:.1f} {units[unit_index]}" if self.reclaimed_bytes else "0 B"
        return (
            f"removed={self.removed_directories}, reclaimed={size_str}"
        )


def save_tlc_log(log_dir, attempt_id, tlc_output):
    log_dir = Path(log_dir)
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / f"attempt_{attempt_id}_tlc_output.txt"
    with open(log_file, "w", encoding="utf-8") as f:
        f.write(tlc_output)
    return str(log_file)

def load_skills(skills_json_path="skills.json"):
    with open(skills_json_path, encoding="utf-8") as f:
        return json.load(f)

def classify_tlc_error(tlc_output, skills_db):
    for skill in skills_db:
        m = re.search(skill["pattern"], tlc_output, re.DOTALL)
        if m:
            return {"key": skill["key"], "strategy": skill["strategy"], "match": m.group(), "groups": m.groupdict()}
    return {"key": "unknown", "strategy": "No skill defined for this error type.", "match": "", "groups": {}}

def parse_tlc_trace(tlc_output: str):
    lines = tlc_output.splitlines()
    violated_invariant = None
    for line in lines:
        m = re.match(r"^Invariant (\w+) is violated", line)
        if m:
            violated_invariant = m.group(1)
            break
    trace_start = None
    for i, line in enumerate(lines):
        if re.match(r"^Trace:", line):
            trace_start = i
            break
    if trace_start is None:
        return None
    trace_lines = []
    for line in lines[trace_start+1:]:
        if line.strip() == "" or line.startswith("Finished"):
            break
        trace_lines.append(line)
    return {
        "violated_invariant": violated_invariant,
        "trace_lines": trace_lines,
        "raw_trace": "\n".join(trace_lines)
    }

def tlc_trace_to_markdown_table(trace_lines):
    out = []
    current_state = ""
    current_vals = []
    for line in trace_lines:
        if line.lstrip().startswith("State "):
            if current_state:
                out.append([current_state, "<br>".join(current_vals)])
            current_state = line.strip(":").strip()
            current_vals = []
        elif line.lstrip().startswith("/\\"):
            current_vals.append(line.strip("/\\ ").replace('"', ''))
    if current_state:
        out.append([current_state, "<br>".join(current_vals)])
    header = "| Step | Variable Assignments |\n|------|----------------------|\n"
    body = "\n".join(f"| {row[0]} | {row[1]} |" for row in out)
    return header + body

def write_violation_report(report_path, attempt_id, violated_inv, tla_inv_code, nl_req, trace, trace_lines, skill, tlc_log_path, llm_explanation=None, llm_plan=None):
    Path(report_path).parent.mkdir(parents=True, exist_ok=True)
    with open(report_path, "w", encoding="utf-8") as f:
        f.write(f"# TLC Error/Violation Report\n\n")
        f.write(f"**Attempt:** {attempt_id}\n\n")
        f.write(f"**Detected Error Type (Skill):** `{skill['key']}`\n")
        f.write(f"**Skill Strategy:** {skill['strategy']}\n\n")
        f.write("## TLC Log File\n")
        f.write(f"[Full TLC log for this attempt]({tlc_log_path})\n\n")
        if violated_inv:
            f.write(f"**Violated Invariant:** `{violated_inv}`\n\n")
        f.write("## Invariant Definition\n")
        f.write(f"```tla\n{tla_inv_code}\n```\n")
        f.write("## Original Natural Language Requirement\n")
        f.write(f"{nl_req}\n\n")
        if trace_lines:
            f.write("## TLC Violation Trace (Markdown Table)\n")
            f.write(tlc_trace_to_markdown_table(trace_lines) + "\n\n")
        if trace:
            f.write("## TLC Raw Trace\n")
            f.write("```\n" + trace + "\n```\n")
        if llm_explanation:
            f.write("## LLM Explanation/Diagnosis\n")
            f.write(llm_explanation + "\n\n")
        if llm_plan:
            f.write("## LLM-Generated Repair Plan\n")
            f.write(llm_plan + "\n\n")

def extract_invariant_code(spec_text, inv_name):
    matches = re.findall(rf"^{inv_name}\s*==[^\n]*(((\n[ \t]+[^=\n]+)+)?)+", spec_text, re.MULTILINE)
    if matches:
        return inv_name + " ==" + matches[0][0]
    return "[definition not found]"


def _coerce_module_dir(module_dir: Path | str) -> Path:
    if isinstance(module_dir, tuple):
        raise TypeError(
            "LoopConfig.module_dir must be path-like; tuple payloads are no longer supported."
        )
    try:
        resolved = Path(module_dir).expanduser().resolve()
    except TypeError as exc:
        raise TypeError("LoopConfig.module_dir must be path-like") from exc
    if not resolved.exists():
        raise FileNotFoundError(f"Module directory '{resolved}' not found.")
    if not resolved.is_dir():
        raise NotADirectoryError(f"Module directory '{resolved}' is not a directory.")
    return resolved


def _resolve_task_artifact(module_dir: Path, artifact: str) -> Path:
    artifact_path = Path(artifact)
    if artifact_path.is_absolute():
        return artifact_path

    direct = module_dir / artifact_path
    if direct.exists():
        return direct

    if artifact_path.parts and artifact_path.parts[0] == module_dir.name:
        stripped = Path(*artifact_path.parts[1:]) if len(artifact_path.parts) > 1 else Path()
        candidate = module_dir / stripped
        if candidate.exists():
            return candidate

    parent_candidate = module_dir.parent / artifact_path
    if parent_candidate.exists():
        return parent_candidate

    matches = [hit for hit in module_dir.rglob(artifact_path.name) if hit.as_posix().endswith(artifact_path.as_posix())]
    if matches:
        return matches[0]

    raise FileNotFoundError(
        f"Unable to locate artifact '{artifact}' relative to module directory '{module_dir}'."
    )


def validate_module_layout(task: TaskSpec, module_dir: Path | str) -> None:
    root = _coerce_module_dir(module_dir)

    # Always copy the bootstrap .cfg template to the destination
    bootstrap_cfg_template = Path(__file__).resolve().parent.parent / "default_bootstrap/BootstrapModule.cfg"
    cfg_target = root / task.cfg_file
    cfg_target.parent.mkdir(parents=True, exist_ok=True)
    _shutil.copy2(bootstrap_cfg_template, cfg_target)
    print(f"[Bootstrap] Copied .cfg config from template at {cfg_target}")

    # Always copy the bootstrap .tla template, with MODULE header rewritten
    bootstrap_tla_template = Path(__file__).resolve().parent.parent / "default_bootstrap/BootstrapModule.tla"
    tla_target = root / f"{task.module_name}.tla"
    with open(bootstrap_tla_template, "r", encoding="utf-8") as src:
        content = src.read()

    content = re.sub(
        r"---- MODULE .* ----",
        f"---- MODULE {task.module_name} ----",
        content,
        count=1
    )
    content = ("\\* AUTOGENERATED FROM BootstrapModule.tla. Replace or edit as needed.\n" + content)
    with open(tla_target, "w", encoding="utf-8") as f:
        f.write(content)
    print(f"[Bootstrap] Copied TLA+ module from template at {tla_target}")

    # (Optional) Manifest file check
    manifest = root / "manifest.json"
    if not manifest.exists():
        warnings.warn(
            f"Optional manifest.json not found in module directory '{root}'.",
            RuntimeWarning,
        )


def _write_module(module_dir: Path | str, module_name: str, spec_text: str, attempt_id: int) -> Path:
    """Ensure MODULE header matches snapshot filename."""
    module_dir = Path(module_dir)
    snapshot_name = f"{module_name}_attempt_{attempt_id}"
    snapshot_path = module_dir / f"{snapshot_name}.tla"
    lines = spec_text.strip().splitlines()
    if lines:
        lines[0] = f"---- MODULE {snapshot_name} ----"
    fixed_body = "\n".join(lines)
    # Save to latest main (optional, for backwards compat)
    target = module_dir / f"{module_name}.tla"
    target.write_text(fixed_body + "\n", encoding="utf-8")
    # Save to snapshot with correct header
    snapshot_path.write_text(fixed_body + "\n", encoding="utf-8")
    print(
        f"[ModuleWrite] attempt={attempt_id} target={target} snapshot={snapshot_path}",
        flush=True,
    )
    return snapshot_path


_QUANTIFIER_BOUND_PATTERN = re.compile(
    r"(\\[AE])(\s+)([A-Za-z_][A-Za-z0-9_]*)(\s+)\\subseteq(\s+)([^:\n\]]+?)(\s*)(?=\s*[:\]])",
    re.MULTILINE,
)


def sanitize_quantifier_bounds(spec_text: str) -> str:
    """Rewrite quantifier bounds that use ``\\subseteq`` into TLC-compatible ``\\in SUBSET`` forms."""

    replacements = 0

    def _replacement(match: re.Match[str]) -> str:
        nonlocal replacements
        replacements += 1
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
    if replacements:
        print(f"[Sanitizer] Rewrote {replacements} quantifier bound(s) to use SUBSET membership.")
    return sanitized


def purge_temp_modules(task_name: str, module_root: Path | str) -> PurgeStats:
    """Remove staged module directories for a task under ``module_root`` and report reclaimed space."""

    root = Path(module_root).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        return PurgeStats()

    prefix = f"{task_name}_"
    removed = 0
    reclaimed_bytes = 0

    for candidate in list(root.iterdir()):
        if not candidate.is_dir() or not candidate.name.startswith(prefix):
            continue
        try:
            for file_path in candidate.rglob("*"):
                if file_path.is_file():
                    try:
                        reclaimed_bytes += file_path.stat().st_size
                    except OSError:
                        continue
            shutil.rmtree(candidate, ignore_errors=False)
            removed += 1
        except Exception as exc:
            warnings.warn(
                f"Failed to purge staged module directory '{candidate}': {exc}",
                RuntimeWarning,
            )
    stats = PurgeStats(removed_directories=removed, reclaimed_bytes=reclaimed_bytes)
    if removed:
        print(f"[ModuleCleanup] {stats.as_log_message()}")
    return stats


# --- Utility: Generate config file from TLA+ module and bootstrap config ---
def generate_cfg_for_tla(tla_path, bootstrap_cfg_path, out_cfg_path):
    with open(tla_path, encoding="utf-8") as f:
        tla_lines = f.readlines()

    constants_declared = set()
    for line in tla_lines:
        mconst = re.match(r"\s*CONSTANTS?\s+([a-zA-Z_][a-zA-Z0-9_, ]*)", line)
        if mconst:
            names = [x.strip() for x in mconst.group(1).split(",")]
            constants_declared.update(names)

    invariant_names = extract_invariants_from_tla(tla_lines)

    init_name, next_name = None, None
    for line in tla_lines:
        m = re.match(r"\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*==", line)
        if m:
            opname_l = m.group(1).lower()
            if opname_l == "init":
                init_name = m.group(1)
            elif opname_l == "next":
                next_name = m.group(1)

    with open(bootstrap_cfg_path, encoding="utf-8") as f:
        cfg_in = f.readlines()
    output_lines = []
    for l in cfg_in:
        if "INIT <InitPredicateName>" in l and init_name:
            output_lines.append(f"INIT {init_name}\n")
        elif "NEXT <NextPredicateName>" in l and next_name:
            output_lines.append(f"NEXT {next_name}\n")
        elif "INVARIANT <TypeOK or something>" in l:
            if "TypeOK" in invariant_names:
                output_lines.append("INVARIANT TypeOK\n")
        elif re.match(r"\s*INVARIANTS?", l, re.IGNORECASE):
            if invariant_names:
                output_lines.append("INVARIANTS\n")
                for inv in invariant_names:
                    output_lines.append(f"    {inv}\n")
        elif l.strip().startswith("CONSTANT") or l.strip().startswith("CONSTANTS"):
            if constants_declared:
                output_lines.append("CONSTANT " + ", ".join(constants_declared) + "\n")
        elif l.strip() == "CONSTANT":
            if constants_declared:
                output_lines.append("CONSTANT " + ", ".join(constants_declared) + "\n")
        else:
            if l.strip() != "" and not l.strip().startswith("*"):
                output_lines.append(l)
    with open(out_cfg_path, "w", encoding="utf-8") as f:
        for l in output_lines:
            f.write(l)
    return out_cfg_path





# AUTO-STUB: Ensure all invariants from config are present in the spec
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
        print(f"[Auto-Stub] Adding stubs for missing invariants: {missing}")
        stubs = [f"{name} == TRUE" for name in sorted(missing)]
        return spec_text.strip() + "\n" + "\n".join(stubs) + "\n"
    else:
        return spec_text
    
# Compute case_metrics as before
def get_failure_classes_from_attempt(attempt):
    key = None
    output = getattr(attempt, "feedback_excerpt", None) or getattr(attempt, "status", None)
    if output:
        try:
            skills_db = load_skills("skills.json")
            key = classify_tlc_error(str(output), skills_db).get("key", "unknown")
        except Exception:
            key = "unknown"
    # Always surface unknown key now
    return [key] if key else []


# Auto-patch .cfg for missing CONSTANT assignments
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
        print(f"[Auto-Config] Adding default assignments in .cfg for: {missing}")
        new_lines = [f"CONSTANT {const} = 3" for const in sorted(missing)]
        base = Path(cfg_path)
        temp_cfg_path = str(base.parent / (base.stem + f".autofill_{attempt_id}.cfg"))
        with open(temp_cfg_path, "w", encoding="utf-8") as f:
            f.write("\n".join(cfg_lines + new_lines) + "\n")
        return temp_cfg_path
    else:
        return cfg_path

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

def generate_cfg_via_llm(module_snapshot, task, provider, attempt_id, prompts_dir, cfg_generation_template=None):
    """
    Generates a TLC .cfg file by prompting the LLM directly,
    instead of using the standard patch/process logic.
    """
    # Compose the input prompt for the LLM
    prompt_template = cfg_generation_template if cfg_generation_template is not None else load_prompt_template(prompts_dir, "cfg_generation")
    with open(module_snapshot, "r", encoding="utf-8") as f:
        tla_contents = f.read()
    llm_prompt = render_prompt(
        prompt_template,
        {
            "tla_module": tla_contents,
            "task_name": task.name,
            "task_requirements": task.requirement_text,
            "example_config": "",
        }
    )
    # Ask LLM to generate .cfg
    llm_response = provider.generate(llm_prompt, {"attempt_id": str(attempt_id), "phase": "generate_cfg"})
    # Write result to cfg file
    out_cfg_path = module_snapshot.with_suffix(".llm.cfg")
    with open(out_cfg_path, "w", encoding="utf-8") as f:
        f.write(llm_response)
    print(f"[LLM-CFG] Wrote LLM-generated TLC config to {out_cfg_path}")
    return str(out_cfg_path)


def remove_invariants_if_undefined(spec_text: str, cfg_path: str) -> None:
    # Defensive cleanup: Always remove literal dummy invariants lines
    with open(cfg_path, encoding="utf-8") as f:
        cfg_text = f.read()
    new_cfg = re.sub(r"^\\s*INVARIANTS?\\s+invariants\\b.*(?:\\n)?", "", cfg_text, flags=re.MULTILINE | re.IGNORECASE)
    if cfg_text != new_cfg:
        with open(cfg_path, "w", encoding="utf-8") as f:
            f.write(new_cfg)
        print(f"[Patcher] Cleaned dummy 'invariants' entry from {cfg_path}")

def run_experiment(
    task: TaskSpec,
    config: LoopConfig,
    prompts_dir: str,
    provider: LLMProvider,
    mode: str,
    *,
    human_intervention_callback: Optional[Callable[[AttemptRecord], bool]] = None,
    learning_step_index: Optional[int] = None,
    apply_patch: bool = True,
) -> Dict[str, str]:

    overall_start_time = time.time()

    unpatched_attempts = []


    if mode not in {"baseline", "loop"}:
        raise ValueError("mode must be 'baseline' or 'loop'")

    module_dir = _coerce_module_dir(config.module_dir)
    validate_module_layout(task, module_dir)

    # Optionally set random seed for reproducibility if supported by provider/backend
    seed = getattr(config, "seed", None)
    if seed is not None:
        random.seed(seed)
        try:
            np.random.seed(seed)
        except ImportError:
            pass

    initial_prompt_name = config.prompt_mode
    initial_template = load_prompt_template(prompts_dir, initial_prompt_name)

    current_prompt = render_prompt(
        initial_template,
        {
            "system_text": task.system_text,
            "requirement_text": task.requirement_text,
            "module_name": task.module_name,
            "previous_spec": "",
            "tool_feedback": "",
        },
    )

    # Eagerly load baseline LLM .cfg generation prompt up front if patching is OFF (for baseline mode)
    cfg_generation_template = None
    if not apply_patch:
        try:
            cfg_generation_template = load_prompt_template(prompts_dir, "cfg_generation")
        except Exception as e:
            raise RuntimeError(f"[ConfigGen] Could not load prompt 'cfg_generation' from {prompts_dir}: {e}")


    result = RunResult(
        task_name=task.name,
        prompt_mode=config.prompt_mode,
        terminal_status="unknown",
        learning_step_index=learning_step_index,
    )

    max_iterations = 1 if mode == "baseline" else config.max_iterations
    latest_spec = ""
    outstanding_counterexamples = 0

    # Checkpoint gated logic for loop mode
    checkpoint_gated = getattr(config, "checkpoint_gated", False)
    total_counterexamples_seen = 0
    total_counterexamples_resolved = 0
    applied_skill_keys: list[str] = []
    successful_skill_uses = 0
    human_intervention_flag = False

    for attempt_id in range(1, max_iterations + 1):
        phase = "generate" if attempt_id == 1 else "repair"
        # --- Timing: attempt overall ---
        attempt_timing = {}
        attempt_timing["start_attempt"] = time.time()

        # --- Timing: LLM call ---
        attempt_timing["start_llm"] = time.time()

        generated = provider.generate(current_prompt, {"attempt_id": str(attempt_id), "phase": phase})



        if apply_patch:
            # Patch the SPEC only here (one-pass)
            latest_spec = generated
            latest_spec = re.sub(r"([a-zA-Z_][a-zA-Z0-9_]*)''", r"\1'", latest_spec)
            latest_spec = sanitize_quantifier_bounds(latest_spec)
            # Optionally: auto-stub missing invariants (if you want), or skip if you want pure removal instead
            # latest_spec = ensure_invariants(latest_spec, ...)  

        else:
            latest_spec = generated
            unpatched_attempts.append(latest_spec)

        # Now write the fully patched spec to disk
        module_snapshot = _write_module(module_dir, task.module_name, latest_spec, attempt_id)
        module_snapshot_str = str(module_snapshot)
        snapshot_name = f"{task.module_name}_attempt_{attempt_id}"

        if apply_patch:
            # Standard deterministic config gen logic:
            bootstrap_cfg_path = Path(__file__).resolve().parent.parent / "default_bootstrap/BootstrapModule.cfg"
            out_cfg_path = module_dir / f"{snapshot_name}.cfg"
            generated_cfg_path = generate_cfg_for_tla(str(module_snapshot), str(bootstrap_cfg_path), str(out_cfg_path))
            remove_invariants_if_undefined(latest_spec, str(generated_cfg_path))
            generated_cfg_path = patch_cfg_with_constants(latest_spec, str(generated_cfg_path), str(attempt_id))
        else:
            # Use preloaded LLM-generated config prompt
            generated_cfg_path = generate_cfg_via_llm(
                module_snapshot, task, provider, attempt_id, prompts_dir, cfg_generation_template=cfg_generation_template
            )

        attempt_timing["end_llm"] = time.time()
        attempt_timing["duration_llm"] = attempt_timing["end_llm"] - attempt_timing["start_llm"]


        metadir = str(module_dir / f".tlc_{task.name}_attempt_{attempt_id}")
        # Instead of module_name, always use the actual snapshot file (w/o .tla extension) as TLC main module

        # --- Timing: TLC call ---
        attempt_timing["start_tlc"] = time.time()
        tlc = run_tlc(
            tla_jar_path=config.tla_jar_path,
            module_dir=str(module_dir),
            module_name=snapshot_name,  # <--- always match file's MODULE header and filename
            cfg_file=generated_cfg_path,
            metadir=metadir,
            timeout_seconds=config.timeout_seconds,
        )
        attempt_timing["end_tlc"] = time.time()
        attempt_timing["duration_tlc"] = attempt_timing["end_tlc"] - attempt_timing["start_tlc"]



        # Checkpoint gated: if enabled and TLC passes, break early (loop mode only)
        if checkpoint_gated and mode == "loop" and tlc.status == "success":
            result.terminal_status = tlc.status
            attempt_record = AttemptRecord(
                attempt_id=attempt_id,
                phase=phase,
                prompt_name=initial_prompt_name if attempt_id == 1 else "repair",
                module_file=module_snapshot_str,
                status=tlc.status,
                parse_ok=tlc.parse_ok,
                semantic_ok=tlc.semantic_ok,
                invariants_violated=tlc.invariants_violated,
                error_count=len(tlc.errors),
                feedback_excerpt="Early stop: checkpoint gated TLC success.",
            )
            result.attempts.append(attempt_record)
            break

        # Improved feedback_excerpt: prioritize real TLC errors/warnings/violations:
        lines = [line for line in tlc.output.splitlines() if line.strip()]
        error_lines = [
            l
            for l in lines
            if (
                "Error:" in l
                or "error" in l.lower()
                or "Exception" in l
                or "violation" in l.lower()
                or "violated" in l.lower()
            )
        ]
        if error_lines:
            excerpt = "\n".join(error_lines)
        else:
            excerpt = "\n".join(lines[:8])
        attempt_record = AttemptRecord(
            attempt_id=attempt_id,
            phase=phase,
            prompt_name=initial_prompt_name if attempt_id == 1 else "repair",
            module_file=module_snapshot_str,
            status=tlc.status,
            parse_ok=tlc.parse_ok,
            semantic_ok=tlc.semantic_ok,
            invariants_violated=tlc.invariants_violated,
            error_count=len(tlc.errors),
            feedback_excerpt=excerpt,
        )

       # --- TLC Log handling ---
        attempt_log_dir = Path(config.output_dir) / "logs"
        tlc_log_path = save_tlc_log(attempt_log_dir, attempt_id, tlc.output)

        if "constant parameter" in tlc.output and "not assigned a value" in tlc.output:
            patched_cfg_path = patch_cfg_with_constants(latest_spec, str(generated_cfg_path), str(attempt_id))
            if str(patched_cfg_path) != str(generated_cfg_path):
                print(f"[Auto-Config-Repatch] Detected unassigned constant, patched config: {patched_cfg_path}")
                generated_cfg_path = patched_cfg_path
                attempt_timing["start_tlc_patch"] = time.time()
                tlc = run_tlc(
                    tla_jar_path=config.tla_jar_path,
                    module_dir=str(module_dir),
                    module_name=snapshot_name,
                    cfg_file=generated_cfg_path,
                    metadir=metadir,
                    timeout_seconds=config.timeout_seconds,
                )
                attempt_timing["end_tlc_patch"] = time.time()
                attempt_timing["duration_tlc_patch"] = attempt_timing["end_tlc_patch"] - attempt_timing["start_tlc_patch"]
                tlc_log_path = save_tlc_log(attempt_log_dir, f"{attempt_id}_autofill", tlc.output)


        # --- Skill classification ---
        skills_db = load_skills("skills.json")
        skill = classify_tlc_error(tlc.output, skills_db)
        if skill["key"] != "unknown":
            attempt_record.skills_applied.append(skill["key"])
            applied_skill_keys.append(skill["key"])

        # Attempt final time
        attempt_timing["end_attempt"] = time.time()
        attempt_timing["duration_total"] = attempt_timing["end_attempt"] - attempt_timing["start_attempt"]
        attempt_timing["duration_engineering_overhead"] = (
            attempt_timing["duration_total"]
            - attempt_timing["duration_llm"]
            - attempt_timing["duration_tlc"]
        )
                # Attach to attempt_record (only works if it's mutable/dataclass)
        if hasattr(attempt_record, "__dict__"):
            attempt_record.timing = attempt_timing
        # For all runs with any error, write violation/error report with trace, skill info, and TLC log
        report_needed = tlc.status != "success" or skill["key"] != "unknown"
        if report_needed:
            trace_data = parse_tlc_trace(tlc.output)
            if trace_data:
                violated_inv = trace_data["violated_invariant"]
                trace_raw = trace_data["raw_trace"]
                tla_inv_code = (
                    extract_invariant_code(latest_spec, violated_inv)
                    if violated_inv
                    else "[definition not found]"
                )
                trace_lines = trace_data["trace_lines"]
                attempt_record.counterexamples_seen = 1
                outstanding_counterexamples += 1
                total_counterexamples_seen += 1
            else:
                violated_inv, trace_raw, tla_inv_code, trace_lines = None, "", "", []
            nl_req = task.requirement_text

            violations_dir = Path(config.output_dir) / "violations"
            violations_dir.mkdir(parents=True, exist_ok=True)
            report_path = violations_dir / f"attempt_{attempt_id}_error_report.md"

            write_violation_report(
                report_path,
                attempt_id,
                violated_inv,
                tla_inv_code,
                nl_req,
                trace_raw,
                trace_lines,
                skill,
                tlc_log_path,
                llm_explanation=None,
                llm_plan=None,
            )
            print(f"[AgenticLoop] Error/violation report written: {report_path}\n")

        if attempt_id == 1:
            result.generation_success = attempt_record.parse_ok and attempt_record.semantic_ok
            result.initial_verification_success = tlc.status == "success"

        if tlc.status == "success" and outstanding_counterexamples > 0:
            attempt_record.counterexamples_resolved = outstanding_counterexamples
            total_counterexamples_resolved += outstanding_counterexamples
            outstanding_counterexamples = 0

        if tlc.status == "success" and attempt_record.skills_applied:
            attempt_record.skills_successful = True
            successful_skill_uses += 1

        if human_intervention_callback is not None:
            try:
                attempt_record.human_intervention = bool(
                    human_intervention_callback(attempt_record)
                )
            except Exception:
                attempt_record.human_intervention = False

        result.attempts.append(attempt_record)
        if attempt_record.human_intervention:
            human_intervention_flag = True

        if tlc.status in {"success", "invariant_violation", "tool_missing", "timeout"}:
            result.terminal_status = tlc.status
            break

        if attempt_id == max_iterations:
            result.terminal_status = tlc.status
            break

        repair_prompt_name = "fix_parse" if tlc.status == "parse_error" else "fix_semantic"
        repair_template = load_prompt_template(prompts_dir, repair_prompt_name)
        current_prompt = render_prompt(
            repair_template,
            {
                "system_text": task.system_text,
                "requirement_text": task.requirement_text,
                "module_name": task.module_name,
                "previous_spec": latest_spec,
                "tool_feedback": tlc.output,
            },
        )

    if result.terminal_status == "unknown":
        result.terminal_status = "incomplete"

    if result.attempts:
        first_attempt = result.attempts[0]
        if not result.generation_success:
            result.generation_success = first_attempt.parse_ok and first_attempt.semantic_ok
        if not result.initial_verification_success:
            result.initial_verification_success = first_attempt.status == "success"

    result.repair_iterations = max(0, len(result.attempts) - 1)
    result.counterexamples_seen = total_counterexamples_seen
    result.counterexamples_resolved = total_counterexamples_resolved
    result.skills_applied = applied_skill_keys
    result.skills_successful = successful_skill_uses
    result.human_intervention = human_intervention_flag

    result.metadata = {
        "module_dir": str(module_dir),
        "cfg_file": task.cfg_file,
        "mode": mode,
        "max_iterations": str(max_iterations),
    }

    if learning_step_index is not None:
        result.metadata["learning_step_index"] = str(learning_step_index)


    path_dict = persist_run_result(result, str(config.output_dir))


    case_metrics = {}
    try:
        case_id = f"{task.name}_trial_{getattr(config, 'seed', 'na')}"
        initial_candidate = result.attempts[0].module_file if result.attempts else None
        initial_status = {
            "parse": result.attempts[0].parse_ok if result.attempts else None,
            "semantic": result.attempts[0].semantic_ok if result.attempts else None,
            "tlc": result.attempts[0].status == "success" if result.attempts else None
        }
        final_status = {
            "parse": result.attempts[-1].parse_ok if result.attempts else None,
            "semantic": result.attempts[-1].semantic_ok if result.attempts else None,
            "tlc": result.terminal_status == "success"
        } if result.attempts else {}


        # No filtering of "unknown" here!
        initial_fail_classes = get_failure_classes_from_attempt(result.attempts[0]) if result.attempts else []
        final_fail_classes = get_failure_classes_from_attempt(result.attempts[-1]) if (result.attempts and result.terminal_status != "success") else []

        repair_success = (not (initial_status.get("tlc") or False)) and final_status.get("tlc", False)
        repair_success = bool(repair_success)
        case_metrics = {
            "case_id": case_id,
            "mode": config.prompt_mode,
            "initial_candidate": initial_candidate,
            "initial_status": initial_status,
            "final_status": final_status,
            "repair_attempts": result.repair_iterations,
            "repair_success": repair_success,
            "initial_failure_classes": initial_fail_classes,
            "resolved_failure_classes": [c for c in initial_fail_classes if c not in final_fail_classes] if initial_fail_classes else [],
            "remaining_failure_classes": final_fail_classes,
            "artifact_dir": str(config.output_dir)
        }
    except Exception as err:
        print(f"[CaseMetrics-Error] {err}")


    # Call persist_run_result as before, getting the returned dict (contains file paths including output JSON file)

    run_result_paths = persist_run_result(result, str(config.output_dir))
    # Patch the JSON on disk to add case_metrics, only if that file exists
    run_json_path = run_result_paths.get("json")
    if run_json_path and os.path.exists(run_json_path):
        with open(run_json_path, "r", encoding="utf-8") as f:
            run_json = json.load(f)
        run_json["case_metrics"] = case_metrics
        with open(run_json_path, "w", encoding="utf-8") as f:
            json.dump(run_json, f, indent=2)
    else:
        print(f"[WARN] Output JSON not found for patching case_metrics: {run_json_path}")


    overall_end_time = time.time()
    result.metadata["overall_duration"] = str(overall_end_time - overall_start_time)
    result.metadata["per_attempt_timings"] = json.dumps(
        [getattr(a, "timing", {}) for a in result.attempts]
    )
    return run_result_paths




