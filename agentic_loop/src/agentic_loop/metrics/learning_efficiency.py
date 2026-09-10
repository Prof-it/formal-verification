"""Logic for loading/aggregating learning efficiency from run JSONs."""

from typing import List, Dict, Any
from pathlib import Path
import json

def load_learning_series(paths: List[Path]) -> List[Dict[str, Any]]:
    series: List[Dict[str, Any]] = []
    for path in paths:
        if path.is_file():
            with open(str(path), "r", encoding="utf-8") as f:
                series.append(json.load(f))
    return series

def collect_learning_series(args) -> List[Dict[str, Any]]:
    candidate_paths: List[Path] = []
    if getattr(args, "learning_series_dir", None):
        dir_path = Path(args.learning_series_dir)
        if dir_path.is_dir():
            candidate_paths.extend(sorted(dir_path.glob("*.json")))
    if getattr(args, "learning_series", None):
        for entry in args.learning_series:
            candidate_paths.append(Path(entry))
    # Deduplicate
    seen = set()
    ordered_paths = []
    for p in candidate_paths:
        if p not in seen:
            ordered_paths.append(p)
            seen.add(p)
    return load_learning_series(ordered_paths)

def compute_learning_efficiency(series: List[Dict[str, Any]]) -> Dict[str, Any]:
    if not series:
        return {
            "count": 0,
            "learning_efficiency": 0.0,
            "initial_accuracy": 0,
            "final_accuracy": 0,
            "step_span": 0,
        }
    def step_index(run: Dict[str, Any], fallback: int) -> int:
        metadata = run.get("metadata", {}) or {}
        value = metadata.get("learning_step_index")
        if value is None:
            return fallback
        try:
            return int(value)
        except (TypeError, ValueError):
            return fallback
    ordered = sorted(
        ((run, step_index(run, idx)) for idx, run in enumerate(series)),
        key=lambda item: item[1],
    )
    step_indices = [idx for _, idx in ordered]
    accuracies = [1 if run.get("terminal_status") == "success" else 0 for run, _ in ordered]
    initial_accuracy = accuracies[0]
    final_accuracy = accuracies[-1]
    step_span = max(step_indices[-1] - step_indices[0], len(series) - 1)
    learning_eff = (final_accuracy - initial_accuracy) / step_span if step_span else float(final_accuracy - initial_accuracy)
    return {
        "count": len(series),
        "learning_efficiency": learning_eff,
        "initial_accuracy": initial_accuracy,
        "final_accuracy": final_accuracy,
        "step_span": step_span,
    }