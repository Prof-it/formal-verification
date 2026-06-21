from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Dict

from .models import RunResult


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
            ],
        )
        writer.writeheader()
        for attempt in run.attempts:
            writer.writerow(attempt.__dict__)

    return {"json": str(json_path), "csv": str(csv_path)}
