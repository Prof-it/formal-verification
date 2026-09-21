from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Dict, List

from .models import RunResult
from .utils.trace_utils import parse_tlc_trace, tlc_trace_to_markdown_table

def _serialize_skills(skills: List[str]) -> str:
    return ",".join(skills)


def persist_run_result(run: RunResult, output_dir: str) -> Dict[str, str]:
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)

    json_path = out / f"{run.task_name}_run.json"
    csv_path = out / f"{run.task_name}_attempts.csv"

    payload = {
        "task_name": run.task_name,
        "prompt_mode": run.prompt_mode,
        "terminal_status": run.terminal_status,
        "parse_success_rate": run.parse_success_rate,
        "semantic_success_rate": run.semantic_success_rate,
        "generation_success": run.generation_success,
        "initial_verification_success": run.initial_verification_success,
        "repair_iterations": run.repair_iterations,
        "counterexamples_seen": run.counterexamples_seen,
        "counterexamples_resolved": run.counterexamples_resolved,
        "skills_applied": run.skills_applied,
        "skills_successful": run.skills_successful,
        "learning_step_index": run.learning_step_index,
        "human_intervention": run.human_intervention,
        "metadata": run.metadata,
        "attempts": [a.__dict__ for a in run.attempts],
    }
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "attempt_id",
                "phase",
                "prompt_name",
                "module_file",
                "status",
                "parse_ok",
                "semantic_ok",
                "invariants_violated",
                "error_count",
                 "feedback_excerpt",
                 "counterexamples_seen",
                 "counterexamples_resolved",
                 "skills_applied",
                 "skills_successful",
                 "human_intervention",
            ],
        )
        writer.writeheader()
        for attempt in run.attempts:
            row = attempt.__dict__.copy()
            row.pop("timing", None)
            row["skills_applied"] = ",".join(attempt.skills_applied)
            writer.writerow(row)

    return {"json": str(json_path), "csv": str(csv_path)}

def write_violation_report(
        report_path, attempt_id, violated_inv, tla_inv_code, nl_req, trace, trace_lines,
        skill, tlc_log_path, llm_explanation=None, llm_plan=None):
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
