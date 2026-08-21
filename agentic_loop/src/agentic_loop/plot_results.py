"""Generate publication-ready figures for agentic loop experiments."""

import argparse
import json
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

import matplotlib.pyplot as plt
from matplotlib.figure import Figure


def _load_json(path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Expected run artifact at {path} — run the experiment first.")
    return json.loads(path.read_text())


def _ensure_output_dir(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    return path


def _save_figure(fig: Figure, directory: Path, stem: str) -> None:
    for ext in ("pdf", "png"):
        fig.savefig(str(directory / f"{stem}.{ext}"), bbox_inches="tight", dpi=300 if ext == "png" else None)
    plt.close(fig)


def _dedupe_paths(paths: Iterable[Path]) -> List[Path]:
    seen: set[str] = set()
    result: List[Path] = []
    for path in paths:
        key = str(path)
        if key not in seen:
            seen.add(key)
            result.append(path)
    return result


def _candidate_run_paths(results_root: Path, task: str, mode_aliases: Sequence[str]) -> List[Path]:
    filename = f"{task}_run.json"
    base_dirs = [
        results_root / "comparison" / task,
        results_root / "comparison",
        results_root / task,
        results_root,
    ]

    parent = results_root.parent
    if parent != results_root:
        base_dirs.extend(
            [
                parent / "comparison" / task,
                parent / "comparison",
                parent / task,
                parent,
            ]
        )

    deduped_bases = _dedupe_paths(base_dirs)
    candidates: List[Path] = []
    for base in deduped_bases:
        direct_added = False
        for alias in mode_aliases:
            if alias:
                candidates.append(base / alias / filename)
            else:
                candidates.append(base / filename)
                direct_added = True
        if not direct_added:
            candidates.append(base / filename)

        comparison_root = base / "comparison"
        if comparison_root.is_dir():
            for run_path in comparison_root.rglob(filename):
                candidates.append(run_path)

    return _dedupe_paths(candidates)


def _resolve_run_json(
    label: str,
    results_root: Path,
    task: str,
    mode_aliases: Sequence[str],
    optional: bool = False,
) -> Tuple[Optional[Dict[str, Any]], Optional[Path]]:
    candidates = _candidate_run_paths(results_root, task, mode_aliases)
    for path in candidates:
        if path.exists():
            return _load_json(path), path

    search_list = "\n".join(f"  - {candidate}" for candidate in candidates)
    if optional:
        print(
            f"[plot_results] Skipping {label} artifacts for task '{task}'; no run JSON found under {results_root}.\n"
            f"Searched:\n{search_list}"
        )
        return None, None

    raise FileNotFoundError(
        f"Expected {label} run artifact for task '{task}' relative to {results_root}.\nChecked paths:\n{search_list}"
    )


def _success_vector(attempts: Iterable[Dict[str, Any]], length: int) -> List[int]:
    vec = [1 if att.get("status") == "success" else 0 for att in attempts]
    if not vec:
        vec = [0]
    while len(vec) < length:
        vec.append(vec[-1])
    return vec


def _plot_verification_learning_curve(loop_run: Dict[str, Any], out_dir: Path) -> None:
    loop_attempts = loop_run.get("attempts", [])
    iterations = list(range(len(loop_attempts))) or [0]
    verification_success = _success_vector(loop_attempts, len(iterations))

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(iterations, verification_success, marker="o", label="Verification success")
    ax.set_xticks(iterations)
    ax.set_yticks([0, 1], ["0%", "100%"])
    ax.set_ylim(-0.1, 1.1)
    ax.set_xlabel("Refinement iteration")
    ax.set_ylabel("Verification success")
    ax.set_title("Verification success over iterative repair")
    ax.grid(True, axis="y", linestyle="--", alpha=0.4)
    ax.legend()

    _save_figure(fig, out_dir, "verification_learning_curve")


def _plot_skill_memory_ablation(loop_run: Dict[str, Any], replay_run: Optional[Dict[str, Any]], out_dir: Path) -> None:
    if not replay_run:
        print("[plot_results] Skipping skill memory ablation plot; replay artifacts unavailable.")
        return

    loop_attempts = loop_run.get("attempts", [])
    replay_attempts = replay_run.get("attempts", [])
    horiz_len = max(len(loop_attempts), len(replay_attempts)) or 1
    iterations = list(range(horiz_len))

    loop_vec = _success_vector(loop_attempts, horiz_len)
    replay_vec = _success_vector(replay_attempts, horiz_len)

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(iterations, replay_vec, marker="s", label="Repair-only (replay)")
    ax.plot(iterations, loop_vec, marker="o", label="Full agent (OpenAI)")
    ax.set_xticks(iterations)
    ax.set_yticks([0, 1], ["0%", "100%"])
    ax.set_ylim(-0.1, 1.1)
    ax.set_xlabel("Refinement iteration")
    ax.set_ylabel("Verification success")
    ax.set_title("Impact of skill memory on verification success")
    ax.grid(True, axis="y", linestyle="--", alpha=0.4)
    ax.legend()

    _save_figure(fig, out_dir, "skill_memory_ablation")


def _plot_process_metrics(
    baseline: Dict[str, Any],
    loop_run: Dict[str, Any],
    out_dir: Path,
    replay: Optional[Dict[str, Any]] = None,
) -> None:
    entries: List[Tuple[str, Dict[str, Any]]] = [("Single-pass", baseline)]
    if replay:
        entries.append(("Repair-only", replay))
    entries.append(("Full Agent", loop_run))

    modes = [label for label, _ in entries]
    parse_rates = [float(entry.get("parse_success_rate", 0)) * 100 for _, entry in entries]
    semantic_rates = [float(entry.get("semantic_success_rate", 0)) * 100 for _, entry in entries]
    final_success = [100 if entry.get("terminal_status") == "success" else 0 for _, entry in entries]

    width = 0.25
    x = range(len(modes))
    fig, ax = plt.subplots(figsize=(7, 4))
    ax.bar([xi - width for xi in x], parse_rates, width=width, label="Parse success")
    ax.bar(x, semantic_rates, width=width, label="Semantic success")
    ax.bar([xi + width for xi in x], final_success, width=width, label="Final verification")
    ax.set_xticks(list(x), modes)
    ax.set_ylabel("Success rate (%)")
    ax.set_ylim(0, 110)
    ax.set_title("Process-oriented evaluation metrics")
    ax.legend()

    _save_figure(fig, out_dir, "agent_evaluation_trajectory")


def _plot_final_outcomes(
    baseline: Dict[str, Any],
    loop_run: Dict[str, Any],
    out_dir: Path,
    replay: Optional[Dict[str, Any]] = None,
) -> None:
    entries: List[Tuple[str, Dict[str, Any]]] = [("Single-pass", baseline)]
    if replay:
        entries.append(("Repair-only", replay))
    entries.append(("Full Agent", loop_run))

    modes = [label for label, _ in entries]
    statuses = [entry.get("terminal_status", "unknown") for _, entry in entries]

    status_colors = {
        "success": "#2E7D32",
        "tlc_error": "#C62828",
        "semantic_error": "#EF6C00",
        "parse_error": "#6A1B9A",
        "invariant_violation": "#283593",
        "unknown": "#616161",
    }

    x_positions = range(len(modes))
    colors = [status_colors.get(status, status_colors["unknown"]) for status in statuses]

    fig, ax = plt.subplots(figsize=(6, 3))
    ax.bar(x_positions, [1] * len(modes), color=colors)
    ax.set_xticks(list(x_positions), modes)
    ax.set_ylim(0, 1)
    ax.set_yticks([])
    ax.set_ylabel("")
    ax.set_title("Final run outcomes")
    ax.grid(False)

    bright_statuses = {"success", "tlc_error", "semantic_error", "invariant_violation"}
    for idx, status in enumerate(statuses):
        label = status.replace("_", " ").title()
        text_color = "white" if status in bright_statuses else "black"
        ax.text(idx, 0.5, label, ha="center", va="center", fontsize=11, color=text_color, fontweight="bold")

    _save_figure(fig, out_dir, "final_outcomes")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-root", type=Path, default=Path("results"),
                        help="Directory containing experiment artifacts (default: results)")
    parser.add_argument("--task", default="nasa_ddmr26", help="Task identifier used in filenames")
    parser.add_argument("--output-dir", type=Path, default=Path("figures"),
                        help="Directory to write generated figures (default: figures)")
    return parser.parse_args()


def main() -> None:
    args = _parse_args()

    results_root = args.results_root
    task = args.task
    output_dir = _ensure_output_dir(args.output_dir)

    baseline, baseline_path = _resolve_run_json("baseline", results_root, task, ("baseline",))
    loop_run, loop_path = _resolve_run_json("loop", results_root, task, ("loop",))
    replay, replay_path = _resolve_run_json("replay", results_root, task, ("replay_loop", "replay"), optional=True)

    if baseline is None or baseline_path is None:
        raise RuntimeError(
            f"Failed to locate baseline run JSON for task '{task}' under {results_root}."
        )
    if loop_run is None or loop_path is None:
        raise RuntimeError(
            f"Failed to locate loop run JSON for task '{task}' under {results_root}."
        )

    _plot_verification_learning_curve(loop_run, output_dir)
    _plot_skill_memory_ablation(loop_run, replay, output_dir)
    _plot_process_metrics(baseline, loop_run, output_dir, replay)
    _plot_final_outcomes(baseline, loop_run, output_dir, replay)

    print(f"Saved updated figures to {output_dir.resolve()}")


if __name__ == "__main__":
    main()
