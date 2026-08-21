from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Dict, List

from .models import RunResult


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
            row["skills_applied"] = ",".join(attempt.skills_applied)
            writer.writerow(row)

    return {"json": str(json_path), "csv": str(csv_path)}
