from __future__ import annotations

import argparse
import csv
import json
import shutil
import tempfile
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

from .engine import purge_temp_modules, run_experiment, validate_module_layout
from .models import LoopConfig
from .providers import build_provider


TASK_MAPPINGS_PATH = Path("results/task_mappings.json")


@dataclass
class StagedModule:
    root: Path
    task_name: str
    module_root: Path
    cleanup: Optional[Callable[[], None]] = None
    _closed: bool = field(default=False, init=False, repr=False)

    def close(self) -> None:
        self._run_cleanup()

    def _run_cleanup(self) -> None:
        if self._closed:
            return
        self._closed = True
        if self.cleanup:
            try:
                self.cleanup()
            except Exception as exc:
                warnings.warn(f"Failed to cleanup staged module directory '{self.root}': {exc}")

    def __enter__(self) -> "StagedModule":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()


@dataclass(order=True)
class _MappingCandidate:
    score: float
    path: Path
    source: str
    justification: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run baseline and loop modes on one task and generate a consolidated table"
    )
    parser.add_argument("--task", required=True, help="Path to task YAML")
    parser.add_argument("--tla-jar", required=True, help="Path to tla2tools.jar")
    parser.add_argument(
        "--module-root",
        default="modules",
        help="Root directory that stores per-task TLA+ modules (default: %(default)s)",
    )
    parser.add_argument(
        "--module-dir",
        default=None,
        help="Override directory containing .tla/.cfg files for this task (defaults to <module-root>/<task_name>)",
    )
    parser.add_argument(
        "--output-dir",
        default="results/comparison",
        help="Directory for comparison outputs (default: %(default)s)",
    )
    parser.add_argument("--prompts-dir", default="prompts", help="Prompt template directory")
    parser.add_argument("--prompt-mode", choices=["zero_shot", "one_shot"], default="one_shot")
    parser.add_argument("--max-iterations", type=int, default=3)
    parser.add_argument("--timeout-seconds", type=int, default=180)

    parser.add_argument("--provider", choices=["replay", "openai"], default="replay")
    parser.add_argument("--model", default="gpt-5")
    parser.add_argument("--replay-dir", default=None)
    parser.add_argument(
        "--artifact-root",
        default=None,
        help="Root directory for per-task artifacts such as logs and violation reports (defaults to sibling of output-dir)",
    )
    parser.add_argument(
        "--learning-series",
        nargs="*",
        default=None,
        help="Optional list of run JSON files representing sequential learning steps to aggregate learning efficiency.",
    )
    parser.add_argument(
        "--learning-series-dir",
        default=None,
        help="Optional directory containing run JSON files to aggregate learning efficiency (sorted lexicographically).",
    )
    return parser.parse_args()


def _load_task_mapping() -> List[Dict[str, Any]]:
    if not TASK_MAPPINGS_PATH.exists():
        return []
    try:
        return json.loads(TASK_MAPPINGS_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []


def _find_mapping_entry(task_path: Path) -> Optional[Dict[str, Any]]:
    entries = _load_task_mapping()
    task_path_str = str(task_path)
    for entry in entries:
        recorded = entry.get("task_file")
        if not recorded:
            continue
        if recorded.endswith(task_path_str) or task_path_str.endswith(recorded):
            return entry
    return None


def _collect_mapping_candidates(mapping: Dict[str, Any]) -> List[_MappingCandidate]:
    candidates: List[_MappingCandidate] = []

    def _append_from_match(match: Dict[str, Any], source: str) -> None:
        raw_path = match.get("path")
        if not raw_path:
            return
        score_raw = match.get("score", 0)
        try:
            score = float(score_raw)
        except (TypeError, ValueError):
            score = 0.0
        justification = match.get("justification", "")
        candidate_path = Path(raw_path)
        for base in (Path.cwd(), Path.cwd().parent):
            resolved = (base / candidate_path).resolve()
            if resolved.exists():
                candidates.append(
                    _MappingCandidate(
                        score=score,
                        path=resolved,
                        source=source,
                        justification=justification,
                    )
                )
                break

    for match in mapping.get("cfg_matches") or []:
        _append_from_match(match, "cfg")
    for match in mapping.get("module_matches") or []:
        _append_from_match(match, "module")

    candidates.sort(key=lambda c: c.score, reverse=True)
    return candidates


def _infer_toolbox_root(path: Path) -> Path:
    current = path
    if current.is_file():
        current = current.parent
    for ancestor in (current, *current.parents):
        if ancestor.name.endswith(".toolbox"):
            return ancestor
    return current


def _stage_module_dir(task: Path, task_spec: Any, module_root: Path) -> Optional[StagedModule]:
    module_root = module_root.expanduser().resolve()
    module_root.mkdir(parents=True, exist_ok=True)
    purge_temp_modules(task_spec.name, module_root)
    mapping = _find_mapping_entry(task)
    if not mapping:
        return None

    candidates = _collect_mapping_candidates(mapping)
    if not candidates:
        return None

    selected = candidates[0]
    toolbox_root = _infer_toolbox_root(selected.path)
    stage_source = toolbox_root.parent if toolbox_root.parent != toolbox_root else toolbox_root

    tmp_parent = Path(tempfile.mkdtemp(prefix=f"{task_spec.name}_", dir=str(module_root.resolve())))
    staged_source = tmp_parent / stage_source.name
    try:
        shutil.copytree(stage_source, staged_source, dirs_exist_ok=True)
    except Exception as exc:
        shutil.rmtree(tmp_parent, ignore_errors=True)
        warnings.warn(
            f"Failed to stage module directory '{stage_source}' for task '{task_spec.name}': {exc}"
        )
        return None

    staged_toolbox = staged_source / toolbox_root.name if stage_source != toolbox_root else staged_source
    if len(candidates) > 1:
        alt_details = ", ".join(
            f"{cand.path} (score={cand.score}, source={cand.source})" for cand in candidates[1:]
        )
        print(
            f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score}) while other candidates were: {alt_details}"
        )
    else:
        print(f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score})")

    return StagedModule(
        root=staged_toolbox.resolve(),
        task_name=task_spec.name,
        module_root=module_root,
        cleanup=None,
    )


def _resolve_module_dir(
    args: argparse.Namespace, task_path: Path, task_spec: Any
) -> StagedModule:
    module_root = Path(args.module_root).expanduser().resolve()
    if args.module_dir:
        module_dir = Path(args.module_dir)
        if not module_dir.exists():
            raise FileNotFoundError(f"Module directory '{module_dir}' not found.")
        module_dir = module_dir.expanduser().resolve()

        return StagedModule(
            root=module_dir,
            task_name=task_spec.name,
            module_root=module_root,
            cleanup=None,
        )

    candidate = module_root / task_spec.name
    if candidate.exists():
        candidate = candidate.expanduser().resolve()

        return StagedModule(
            root=candidate,
            task_name=task_spec.name,
            module_root=module_root,
            cleanup=None,
        )

    staged_result = _stage_module_dir(task_path, task_spec, module_root)
    if staged_result and staged_result.root.exists():
        return staged_result

    raise FileNotFoundError(
        "Unable to locate module directory. Provide --module-dir or ensure mappings are available."
    )


def _load_json(path: str) -> Dict[str, Any]:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _summarize(run_json: Dict[str, Any], mode: str) -> Dict[str, Any]:
    attempts: List[Dict[str, Any]] = run_json.get("attempts", [])
    last = attempts[-1] if attempts else {}

    gsr = run_json.get("generation_success", False)
    ivsr = run_json.get("initial_verification_success", False)
    repair_iterations = int(run_json.get("repair_iterations", 0))
    counterexamples_seen = int(run_json.get("counterexamples_seen", 0))
    counterexamples_resolved = int(run_json.get("counterexamples_resolved", 0))
    skills_attempted = run_json.get("skills_applied", []) or []
    skills_successful = int(run_json.get("skills_successful", 0))

    verification_gap = int(gsr) - int(ivsr)
    rsr_ind = 0
    if not ivsr:
        rsr_ind = 1 if run_json.get("terminal_status") == "success" else 0
    human_intervention = 1 if run_json.get("human_intervention") else 0

    return {
        "Mode": mode,
        "TerminalStatus": run_json.get("terminal_status", "unknown"),
        "Attempts": len(attempts),
        "ParseSuccessRate": f"{run_json.get('parse_success_rate', 0.0):.3f}",
        "SemanticSuccessRate": f"{run_json.get('semantic_success_rate', 0.0):.3f}",
        "GenerationSuccess": int(gsr),
        "InitialVerificationSuccess": int(ivsr),
        "VerificationGap": verification_gap,
        "RepairSuccess": rsr_ind,
        "RepairIterations": repair_iterations,
        "CounterexamplesSeen": counterexamples_seen,
        "CounterexamplesResolved": counterexamples_resolved,
        "SkillsApplied": len(skills_attempted),
        "SkillsSuccessful": skills_successful,
        "HumanIntervention": human_intervention,
        "FinalParseOK": bool(last.get("parse_ok", False)),
        "FinalSemanticOK": bool(last.get("semantic_ok", False)),
        "FinalInvariantViolation": bool(last.get("invariants_violated", False)),
        "TotalErrors": sum(int(a.get("error_count", 0)) for a in attempts),
    }


def _write_csv(path: Path, rows: List[Dict[str, Any]]) -> None:
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


def _to_markdown(rows: List[Dict[str, Any]]) -> str:
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


def _load_learning_series(paths: List[Path]) -> List[Dict[str, Any]]:
    series: List[Dict[str, Any]] = []
    for path in paths:
        if path.is_file():
            series.append(_load_json(str(path)))
    return series


def _collect_learning_series(args: argparse.Namespace) -> List[Dict[str, Any]]:
    candidate_paths: List[Path] = []
    if args.learning_series_dir:
        dir_path = Path(args.learning_series_dir)
        if dir_path.is_dir():
            candidate_paths.extend(sorted(dir_path.glob("*.json")))
    if args.learning_series:
        for entry in args.learning_series:
            candidate_paths.append(Path(entry))
    # Deduplicate while preserving order
    seen: Set[Path] = set()
    ordered_paths: List[Path] = []
    for p in candidate_paths:
        if p not in seen:
            ordered_paths.append(p)
            seen.add(p)
    return _load_learning_series(ordered_paths)


def _compute_learning_efficiency(series: List[Dict[str, Any]]) -> Dict[str, Any]:
    if not series:
        return {
            "count": 0,
            "learning_efficiency": 0.0,
            "initial_accuracy": 0,
            "final_accuracy": 0,
            "step_span": 0,
        }

    def _step_index(run: Dict[str, Any], fallback: int) -> int:
        metadata = run.get("metadata", {}) or {}
        value = metadata.get("learning_step_index")
        if value is None:
            return fallback
        try:
            return int(value)
        except (TypeError, ValueError):
            return fallback

    ordered = sorted(
        ((run, _step_index(run, idx)) for idx, run in enumerate(series)),
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


def main() -> None:
    args = parse_args()

    from .task_loader import load_task_spec

    task_path = Path(args.task)
    task = load_task_spec(args.task)

    with _resolve_module_dir(args, task_path, task) as module_binding:
        validate_module_layout(task, module_binding.root)
        module_dir = module_binding.root

        artifact_root = (
            Path(args.artifact_root)
            if args.artifact_root
            else Path(args.output_dir).parent / task.name
        )
        root_out = Path(args.output_dir) / task.name
        baseline_out = root_out / "baseline"
        loop_out = root_out / "loop"
        baseline_out.mkdir(parents=True, exist_ok=True)
        loop_out.mkdir(parents=True, exist_ok=True)

        (artifact_root / "logs").mkdir(parents=True, exist_ok=True)
        (artifact_root / "violations").mkdir(parents=True, exist_ok=True)

        num_trials = args.num_trials if args.num_trials and args.num_trials > 0 else 1
        trial_seed_offset = args.trial_seed_offset
        checkpoint_gated = args.checkpoint_gated

        baseline_jsons = []
        loop_jsons = []

        for trial in range(1, num_trials + 1):
            # Set up per-trial output dirs
            baseline_trial_out = baseline_out / f"trial_{trial:02d}"
            loop_trial_out = loop_out / f"trial_{trial:02d}"
            baseline_trial_out.mkdir(parents=True, exist_ok=True)
            loop_trial_out.mkdir(parents=True, exist_ok=True)

            # Optionally set seed for reproducibility
            seed = (trial_seed_offset + trial) if trial_seed_offset is not None else None

            # Baseline mode
            baseline_provider = build_provider(args.provider, args.model, args.replay_dir)
            baseline_cfg = LoopConfig(
                tla_jar_path=args.tla_jar,
                module_dir=module_dir,
                output_dir=baseline_trial_out,
                prompt_mode=args.prompt_mode,
                max_iterations=args.max_iterations,
                timeout_seconds=args.timeout_seconds,
                seed=seed,
            )
            baseline_artifacts = run_experiment(
                task=task,
                config=baseline_cfg,
                prompts_dir=args.prompts_dir,
                provider=baseline_provider,
                mode="baseline",
            )
            baseline_json = _load_json(baseline_artifacts["json"])
            baseline_jsons.append(baseline_json)

            # Loop mode
            loop_provider = build_provider(args.provider, args.model, args.replay_dir)
            loop_cfg = LoopConfig(
                tla_jar_path=args.tla_jar,
                module_dir=module_dir,
                output_dir=loop_trial_out,
                prompt_mode=args.prompt_mode,
                max_iterations=args.max_iterations,
                timeout_seconds=args.timeout_seconds,
                seed=seed,
                checkpoint_gated=checkpoint_gated,
            )
            loop_artifacts = run_experiment(
                task=task,
                config=loop_cfg,
                prompts_dir=args.prompts_dir,
                provider=loop_provider,
                mode="loop",
            )
            loop_json = _load_json(loop_artifacts["json"])
            loop_jsons.append(loop_json)

        # Summarize all trials
        rows = []
        for i in range(num_trials):
            rows.append(_summarize(baseline_jsons[i], f"baseline_trial_{i+1}"))
            rows.append(_summarize(loop_jsons[i], f"loop_trial_{i+1}"))

        csv_path = root_out / f"comparison_{task.name}.csv"
        md_path = root_out / f"comparison_{task.name}.md"
        _write_csv(csv_path, rows)
        md_table = _to_markdown(rows)

        learning_summary = None
        summary_path: Optional[Path] = None
        if args.learning_series or args.learning_series_dir:
            learning_runs = _collect_learning_series(args)
            if learning_runs:
                learning_summary = _compute_learning_efficiency(learning_runs)
                summary_path = root_out / "learning_efficiency_summary.json"
                summary_path.write_text(json.dumps(learning_summary, indent=2), encoding="utf-8")
                md_table += "\n\n### Learning Efficiency Summary\n"
                md_table += "| Runs | InitialAccuracy | FinalAccuracy | StepSpan | LearningEfficiency |\n"
                md_table += "|---:|---:|---:|---:|---:|\n"
                md_table += (
                    f"| {learning_summary['count']} | {learning_summary['initial_accuracy']} | {learning_summary['final_accuracy']} | "
                    f"{learning_summary['step_span']} | {learning_summary['learning_efficiency']:.3f} |\n"
                )
            else:
                print("No learning-series artifacts found; skipping learning efficiency aggregation.")

        md_path.write_text(md_table + "\n", encoding="utf-8")

        print("Comparison completed.")
        print(f"CSV table:     {csv_path}")
        print(f"Markdown:      {md_path}")
        if learning_summary and summary_path:
            print(f"Learning efficiency summary JSON: {summary_path}")
            print("Learning efficiency summary:")
            print(json.dumps(learning_summary, indent=2))
        print("\n" + md_table)


if __name__ == "__main__":
    main()
    parser.add_argument(
        "--num-trials",
        type=int,
        default=1,
        help="Number of stochastic trials per mode (default: 1)",
    )
    parser.add_argument(
        "--trial-seed-offset",
        type=int,
        default=None,
        help="Seed offset for deterministic seeding (optional)",
    )
    parser.add_argument(
        "--checkpoint-gated",
        action="store_true",
        help="If set, stop repair as soon as TLC passes in any iteration (loop mode only)",
    )
