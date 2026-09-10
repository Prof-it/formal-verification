"""CSV and Markdown read/write helpers, refactored."""

import csv
import json
from pathlib import Path
from typing import List, Dict, Any

def write_csv(path: Path, rows: List[Dict[str, Any]]) -> None:
    """Write main comparison CSV table to disk. Refactored from _write_csv."""
    fieldnames = [
        "Mode",
        "TerminalStatus",
        "Attempts",
        "ParseSuccessRate",
        "SemanticSuccessRate",
        "GenerationSuccess",
        "InitialVerificationSuccess",
        "VerificationGap",
        "RepairSuccess",
        "RepairIterations",
        "CounterexamplesSeen",
        "CounterexamplesResolved",
        "SkillsApplied",
        "SkillsSuccessful",
        "HumanIntervention",
        "FinalParseOK",
        "FinalSemanticOK",
        "FinalInvariantViolation",
        "TotalErrors",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)

def write_trial_metrics_csv(csv_path: Path, trial_json: dict, trial_id: int, mode: str, seed=None):
    """
    Write per-trial metrics.csv summarizing trial and all attempts for reporting.
    Refactored from _write_trial_metrics_csv.
    """
    summary_keys = [
        "trial_id",
        "mode",
        "seed",
        "terminal_status",
        "parse_success_rate",
        "semantic_success_rate",
        "generation_success",
        "initial_verification_success",
        "repair_iterations",
        "regression",
        "total_errors",
        "human_intervention"
    ]
    summary = {
        "trial_id": trial_id,
        "mode": mode,
        "seed": seed,
        "terminal_status": trial_json.get("terminal_status"),
        "parse_success_rate": trial_json.get("parse_success_rate"),
        "semantic_success_rate": trial_json.get("semantic_success_rate"),
        "generation_success": trial_json.get("generation_success"),
        "initial_verification_success": trial_json.get("initial_verification_success"),
        "repair_iterations": trial_json.get("repair_iterations"),
        "regression": trial_json.get("regression", None),
        "total_errors": sum(int(a.get("error_count", 0)) for a in trial_json.get("attempts", [])),
        "human_intervention": bool(trial_json.get("human_intervention", False)),
    }
    attempt_cols = [
        "attempt_id", "phase", "prompt_name", "status", "parse_ok", "semantic_ok", "invariants_violated", "error_count"
    ]
    with csv_path.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(summary_keys)
        writer.writerow([summary[k] for k in summary_keys])
        writer.writerow([])
        writer.writerow(["trial_id", "mode"] + attempt_cols)
        for a in trial_json.get("attempts", []):
            writer.writerow([
                trial_id,
                mode,
                a.get("attempt_id"),
                a.get("phase"),
                a.get("prompt_name"),
                a.get("status"),
                a.get("parse_ok"),
                a.get("semantic_ok"),
                a.get("invariants_violated"),
                a.get("error_count")
            ])

def to_markdown(rows: List[Dict[str, Any]]) -> str:
    header = (
        "| Mode | TerminalStatus | Attempts | ParseSuccessRate | SemanticSuccessRate | GenerationSuccess | "
        "InitialVerificationSuccess | VerificationGap | RepairSuccess | RepairIterations | CounterexamplesSeen | "
        "CounterexamplesResolved | SkillsApplied | SkillsSuccessful | HumanIntervention | FinalParseOK | FinalSemanticOK | "
        "FinalInvariantViolation | TotalErrors |"
    )
    divider = "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|---|---:|"
    lines = [header, divider]
    for row in rows:
        lines.append(
            "| {Mode} | {TerminalStatus} | {Attempts} | {ParseSuccessRate} | {SemanticSuccessRate} | "
            "{GenerationSuccess} | {InitialVerificationSuccess} | {VerificationGap} | {RepairSuccess} | {RepairIterations} | {CounterexamplesSeen} | "
            "{CounterexamplesResolved} | {SkillsApplied} | {SkillsSuccessful} | {HumanIntervention} | {FinalParseOK} | {FinalSemanticOK} | {FinalInvariantViolation} | {TotalErrors} |".format(**row)
        )
    return "\n".join(lines)

def write_case_metrics_csv(csv_path: Path, case_metrics_list: List[Dict[str, Any]]) -> None:
    """Write a CSV summarizing per-case/canonical metrics for every run."""
    keys = [
        "case_id", "mode", "initial_candidate", "initial_status", "final_status",
        "repair_attempts", "repair_success",
        "initial_failure_classes", "resolved_failure_classes", "remaining_failure_classes", "artifact_dir"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        for cm in case_metrics_list:
            row = cm.copy()
            for k, v in row.items():
                if isinstance(v, (dict, list)):
                    row[k] = json.dumps(v)
            writer.writerow(row)