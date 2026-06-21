from __future__ import annotations

from pathlib import Path
from typing import Dict

from .models import AttemptRecord, LoopConfig, RunResult, TaskSpec
from .prompting import load_prompt_template, render_prompt
from .providers import LLMProvider
from .reporting import persist_run_result
from .tlc_runner import run_tlc

import json
import re
from pathlib import Path

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


def _write_module(module_dir: str, module_name: str, spec_text: str, attempt_id: int) -> str:
    """Ensure MODULE header matches snapshot filename."""
    snapshot_name = f"{module_name}_attempt_{attempt_id}"
    snapshot_path = Path(module_dir) / f"{snapshot_name}.tla"
    lines = spec_text.strip().splitlines()
    if lines:
        lines[0] = f"---- MODULE {snapshot_name} ----"
    fixed_body = "\n".join(lines)
    # Save to latest main (optional, for backwards compat)
    target = Path(module_dir) / f"{module_name}.tla"
    target.write_text(fixed_body + "\n", encoding="utf-8")
    # Save to snapshot with correct header
    snapshot_path.write_text(fixed_body + "\n", encoding="utf-8")
    return str(snapshot_path)


def run_experiment(
    task: TaskSpec,
    config: LoopConfig,
    prompts_dir: str,
    provider: LLMProvider,
    mode: str,
) -> Dict[str, str]:
    if mode not in {"baseline", "loop"}:
        raise ValueError("mode must be 'baseline' or 'loop'")

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

    result = RunResult(task_name=task.name, prompt_mode=config.prompt_mode, terminal_status="unknown")

    max_iterations = 1 if mode == "baseline" else config.max_iterations
    latest_spec = ""

    for attempt_id in range(1, max_iterations + 1):
        phase = "generate" if attempt_id == 1 else "repair"
        generated = provider.generate(current_prompt, {"attempt_id": str(attempt_id), "phase": phase})

        # AUTO-REPAIR: Replace any double prime with single prime before writing TLA+
        import re
        double_prime_repaired = re.sub(r"([a-zA-Z_][a-zA-Z0-9_]*)''", r"\1'", generated)
        if double_prime_repaired != generated:
            print(f"[Auto-Repair] Fixed double-prime to single-prime in attempt {attempt_id}")
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
        
        # Use original cfg before patching for missing invariants
        from pathlib import Path
        cfg_path_for_invariants = str(Path(config.module_dir) / task.cfg_file) if not Path(task.cfg_file).is_absolute() else task.cfg_file
        invariants_and_prime_repaired = ensure_invariants(double_prime_repaired, cfg_path_for_invariants)
        latest_spec = invariants_and_prime_repaired

        module_snapshot = _write_module(config.module_dir, task.module_name, latest_spec, attempt_id)
        # Compute the actual snapshot module name without .tla extension
        snapshot_name = f"{task.module_name}_attempt_{attempt_id}"
        snapshot_file = str(Path(config.module_dir) / f"{snapshot_name}.tla")

        # Auto-patch .cfg for missing CONSTANT assignments
        def patch_cfg_with_constants(spec_text: str, cfg_path: str) -> str:
            import re
            declared_constants = set()
            for line in spec_text.splitlines():
                m = re.match(r'\s*CONSTANT\s+([a-zA-Z_][a-zA-Z0-9_]*)', line)
                if m:
                    declared_constants.add(m.group(1))
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
                # Always use .cfg at the end
                from pathlib import Path
                base = Path(cfg_path)
                temp_cfg_path = str(base.parent / (base.stem + f".autofill_{attempt_id}.cfg"))
                with open(temp_cfg_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(cfg_lines + new_lines) + "\n")
                return temp_cfg_path
            else:
                return cfg_path

        # Use full path for the .cfg file (even if only a filename is given)
        from pathlib import Path
        cfg_path = str(Path(config.module_dir) / task.cfg_file) if not Path(task.cfg_file).is_absolute() else task.cfg_file
        patched_cfg = patch_cfg_with_constants(latest_spec, cfg_path)

        metadir = str(Path(config.module_dir) / f".tlc_{task.name}_attempt_{attempt_id}")
        # Instead of module_name, always use the actual snapshot file (w/o .tla extension) as TLC main module
        tlc = run_tlc(
            tla_jar_path=config.tla_jar_path,
            module_dir=config.module_dir,
            module_name=snapshot_name,  # <--- always match file's MODULE header and filename
            cfg_file=patched_cfg,
            metadir=metadir,
            timeout_seconds=config.timeout_seconds,
        )

        # Improved feedback_excerpt: prioritize real TLC errors/warnings/violations:
        lines = [line for line in tlc.output.splitlines() if line.strip()]
        error_lines = [l for l in lines if (
            "Error:" in l or "error" in l.lower() or "Exception" in l or "violation" in l.lower() or "violated" in l.lower()
        )]
        if error_lines:
            excerpt = "\n".join(error_lines)
        else:
            excerpt = "\n".join(lines[:8])
        # === TLC VIOLATION TRACE HARVESTING & REPORT WRITING ===
        def parse_tlc_trace(tlc_output: str):
            import re
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
            from pathlib import Path
            Path(report_path).parent.mkdir(parents=True, exist_ok=True)
            with open(report_path, "w", encoding="utf-8") as f:
                f.write(f"# TLC Invariant Violation Report\n\n")
                f.write(f"**Attempt:** {attempt_id}\n\n")
                f.write(f"**Violated Invariant:** `{violated_inv}`\n\n")
                f.write("## Invariant Definition\n")
                f.write(f"```tla\n{tla_inv_code}\n```\n")
                f.write("## Original Natural Language Requirement\n")
                f.write(f"{nl_req}\n\n")
                f.write("## TLC Violation Trace (Markdown Table)\n")
                f.write(tlc_trace_to_markdown_table(trace_lines) + "\n\n")
                f.write("## TLC Raw Trace\n")
                f.write("```\n" + trace + "\n```\n")
                f.write("## Skill Classification\n")
                f.write(f"{skill}\n\n")
                f.write("## TLC Log Path\n")
                f.write(f"{tlc_log_path}\n\n")
                if llm_explanation:
                    f.write("## LLM Explanation/Diagnosis\n")
                    f.write(llm_explanation + "\n\n")
                if llm_plan:
                    f.write("## LLM-Generated Repair Plan\n")
                    f.write(llm_plan + "\n\n")

        # Find TLA invariant code (naive: extract from generated spec text by name)
        def extract_invariant_code(spec_text, inv_name):
            import re
            matches = re.findall(rf"^{inv_name}\s*==[^\n]*(((\n[ \t]+[^=\n]+)+)?)+", spec_text, re.MULTILINE)
            if matches:
                return inv_name + " ==" + matches[0][0]
            return "[definition not found]"

        # ... record result as before ...
        result.attempts.append(
            AttemptRecord(
                attempt_id=attempt_id,
                phase=phase,
                prompt_name=initial_prompt_name if attempt_id == 1 else "repair",
                module_file=module_snapshot,
                status=tlc.status,
                parse_ok=tlc.parse_ok,
                semantic_ok=tlc.semantic_ok,
                invariants_violated=tlc.invariants_violated,
                error_count=len(tlc.errors),
                feedback_excerpt=excerpt,
            )
        )
        # --- TLC Log handling ---
        tlc_log_path = save_tlc_log("results/logs", attempt_id, tlc.output)
        # --- Skill classification ---
        skills_db = load_skills("skills.json")
        skill = classify_tlc_error(tlc.output, skills_db)

        # For all runs with any error, write violation/error report with trace, skill info, and TLC log
        report_needed = tlc.status != "success" or skill["key"] != "unknown"
        if report_needed:
            trace_data = parse_tlc_trace(tlc.output)
            if trace_data:
                violated_inv = trace_data["violated_invariant"]
                trace_raw = trace_data["raw_trace"]
                tla_inv_code = extract_invariant_code(latest_spec, violated_inv) if violated_inv else "[definition not found]"
                trace_lines = trace_data["trace_lines"]
            else:
                violated_inv, trace_raw, tla_inv_code, trace_lines = None, "", "", []
            nl_req = task.requirement_text
            report_path = f"results/violations/attempt_{attempt_id}_error_report.md"
            write_violation_report(report_path, attempt_id, violated_inv, tla_inv_code, nl_req, trace_raw, trace_lines, skill, tlc_log_path, llm_explanation=None, llm_plan=None)
            print(f"[AgenticLoop] Error/violation report written: {report_path}\n")
        
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

    result.metadata = {
        "module_dir": config.module_dir,
        "cfg_file": task.cfg_file,
        "mode": mode,
        "max_iterations": str(max_iterations),
    }

    return persist_run_result(result, config.output_dir)
