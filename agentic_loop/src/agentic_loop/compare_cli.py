
import argparse
import csv
import json
import shutil
import os
import re
import tempfile
import numpy as np
import logging
# At the very TOP of your script, before any logging calls:
logging.basicConfig(level=logging.WARNING)


from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Set
from dotenv import load_dotenv


from .engine import run_experiment, validate_module_layout
from .models import LoopConfig
from .providers import build_provider
from .utils.io_utils import purge_temp_modules
from .core.copy_utils import copytree_symlink_safe
from .metrics.stats_analysis import _is_tlc_success, mcnemar_analysis, mcnemar_csv, mcnemar_markdown, reclassify_attempts_with_final_rules
from .task_loader import load_task_spec
from .utils.timing_utils import collect_all_timings, timing_stats, fmt, fmt_int
from .utils.tlc_error_utils import classify_tlc_error
# Add dotenv support for automatic .env loading
try:
    load_dotenv(dotenv_path=os.path.join(os.path.dirname(__file__), '../../.env'))
except ImportError:
    pass  # If dotenv is not installed, skip loading .env
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
                logging.warning(f"Failed to cleanup staged module directory '{self.root}': {exc}")

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
    parser.add_argument(
        "--no-patch", action="store_true",
        help="If set, disables domain patching (raw LLM output only for both baseline and loop)"
    )

    parser.add_argument(
        "--analyze-only", action="store_true",
        help="If set, only computes statistics/aggregates existing JSON results without running any new experiments"
    )

    return parser.parse_args()


def _log_event_to_csv(csv_path, trial, event_type, attempt_index, mode, details=None):
    """
    Logs repair/regression event to the events CSV file for later analysis.
    """
    header = ["trial", "event_type", "attempt_index", "mode", "details"]
    row = {
        "trial": trial,
        "event_type": event_type,
        "attempt_index": attempt_index,
        "mode": mode,
        "details": json.dumps(details) if details is not None else ""
    }
    write_header = not csv_path.exists()
    with open(csv_path, "a", newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=header)
        if write_header:
            writer.writeheader()
        writer.writerow(row)

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

def _append_from_match(match: Dict[str, Any], source: str, candidates: list) -> None:
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
def _collect_mapping_candidates(mapping: Dict[str, Any]) -> List[_MappingCandidate]:
    candidates: List[_MappingCandidate] = []

    for match in mapping.get("cfg_matches") or []:
        _append_from_match(match, "cfg", candidates)
    for match in mapping.get("module_matches") or []:
        _append_from_match(match, "module", candidates)

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


def _stage_module_dir(task: Path, task_spec: Any, module_root: Path) -> Optional['StagedModule']:
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

    # PROTECTION: Prevent recursive or project-root copy!
    project_root = Path(__file__).resolve()
    for parent in project_root.parents:
        if parent.name == 'agentic_loop':
            project_root = parent.resolve()
            break
    # Do not allow copytree if stage_source is or contains the project root
    if project_root in stage_source.resolve().parents or stage_source.resolve() == project_root:
        logging.warning(
            f"Refusing to recursively stage/copy project root directory '{project_root}' (source: '{stage_source}') for task '{task_spec.name}'."
        )
        return None

    tmp_parent = Path(tempfile.mkdtemp(prefix=f"{task_spec.name}_", dir=str(module_root.resolve())))
    staged_source = tmp_parent / stage_source.name
    try:
        shutil.copytree(stage_source, staged_source, dirs_exist_ok=True)
    except Exception as exc:
        shutil.rmtree(tmp_parent, ignore_errors=True)
        logging.warning(
            f"Failed to stage module directory '{stage_source}' for task '{task_spec.name}': {exc}"
        )
        return None

    staged_toolbox = staged_source / toolbox_root.name if stage_source != toolbox_root else staged_source
    if len(candidates) > 1:
        alt_details = ", ".join(
            f"{cand.path} (score={cand.score}, source={cand.source})" for cand in candidates[1:]
        )
        logging.debug(
            f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score}) while other candidates were: {alt_details}"
        )
    else:
        logging.debug(f"[ModuleStage] Selected '{toolbox_root}' (score={selected.score})")

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

    fresh_moduledir = Path(tempfile.mkdtemp(prefix=f"{task_spec.name}_", dir=str(module_root.resolve())))
    logging.debug(f"[Bootstrap-Module] No input module-dir given; created temp dir: {fresh_moduledir}")
    # Will contain no .tla input, so validate_module_layout/bootstrap fallback will trigger
    return StagedModule(
        root=fresh_moduledir,
        task_name=task_spec.name,
        module_root=module_root,
        cleanup=None,
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

# Metrics writer inserted immediately after imports
def _write_trial_metrics_csv(csv_path: Path, trial_json: dict, trial_id: int, mode: str, seed=None):
    """
    Writes a per-trial metrics.csv summarizing trial and all attempts for reporting and ETECOM reproducibility
    """
    # Overall trial summary row keys
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
    # Derive summary values
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
    # Columns for each attempt
    attempt_cols = [
        "attempt_id", "phase", "prompt_name", "status", "parse_ok", "semantic_ok", "invariants_violated", "error_count"]
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

def _step_index(run: Dict[str, Any], fallback: int) -> int:
    metadata = run.get("metadata", {}) or {}
    value = metadata.get("learning_step_index")
    if value is None:
        return fallback
    try:
        return int(value)
    except (TypeError, ValueError):
        return fallback
    
def _compute_learning_efficiency(series: List[Dict[str, Any]]) -> Dict[str, Any]:
    if not series:
        return {
            "count": 0,
            "learning_efficiency": 0.0,
            "initial_accuracy": 0,
            "final_accuracy": 0,
            "step_span": 0,
        }
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

def _write_case_metrics_csv(csv_path, case_metrics_list):
    """
    Writes out a CSV summarizing per-case/canonical metrics for every run
    """
    keys = [
        "case_id", "mode", "TerminalStatus",
        "initial_candidate", "initial_status", "final_status",
        "repair_attempts", "repair_success",
        "initial_failure_classes", "resolved_failure_classes", "remaining_failure_classes", "artifact_dir"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        for cm in case_metrics_list:
            # Convert substructure to string for csv
            row = cm.copy()
            for k, v in row.items():
                if isinstance(v, (dict, list)):
                    row[k] = json.dumps(v)
            writer.writerow(row)




# Failure class repairability table per mode
def failure_class_table(cases, label):
    failing = [c for c in cases if not (c.get("initial_status") or {}).get("tlc")]
    fc_table = {}
    for case in failing:
        fclist = case.get("initial_failure_classes", [])
        if isinstance(fclist, str):
            try:
                fclist = json.loads(fclist)
            except Exception:
                fclist = []
        for fc in fclist:
            if fc not in fc_table:
                fc_table[fc] = {"total": 0, "repaired": 0}
            fc_table[fc]["total"] += 1
            if (case.get("final_status") or {}).get("tlc"):
                fc_table[fc]["repaired"] += 1
    logging.info(f"\n| Failure class ({label}) | Cases | Repaired | Repairability |")
    logging.info("|----------------------|-------|----------|--------------|")
    for fc, val in sorted(fc_table.items()):
        total = val["total"]
        repaired = val["repaired"]
        rep_rate = (repaired/total)*100 if total > 0 else 0
        logging.info(f"| {fc} | {total} | {repaired} | {rep_rate:.1f}% |")

def extract_stats(cases):
    n_total = len(cases)
    logging.debug(f"extract_stats: examining n_total={n_total}")
    isr_count = sum(1 for c in cases if (c.get("initial_status") or {}).get("tlc"))
    fsr_count = sum(1 for c in cases if (c.get("final_status") or {}).get("tlc"))
    logging.debug(f"  TLC initial_status.tlc = True: {isr_count}")
    logging.debug(f"  TLC final_status.tlc = True: {fsr_count}")
    logging.debug(f"  Terminal statuses: {[c.get('TerminalStatus', '') for c in cases]}")
    failing = [c for c in cases if not (c.get("initial_status") or {}).get("tlc")]
    n_failing = len(failing)
    crsr = sum(1 for c in failing if (c.get("final_status") or {}).get("tlc")) / n_failing if n_failing else 0
    return dict(ISR=isr_count/n_total if n_total > 0 else 0, FSR=fsr_count/n_total if n_total > 0 else 0, CRSR=crsr, n_total=n_total, n_failing=n_failing)

def summarize_case_metrics_per_mode(baseline_cases, loop_cases):
    """
    Print ISR/FSR/CRSR/failure-class repairability per mode side-by-side.
    """
    # Helper for stats extraction
    b_stats = extract_stats(baseline_cases)
    l_stats = extract_stats(loop_cases)

    logging.info("\nSuccess Rate Comparison (per mode):")
    logging.info("| Metric | Baseline | Loop |")
    logging.info("|--------|----------|------|")
    logging.info(f"| ISR    | {b_stats['ISR']:.2%} ({sum(1 for c in baseline_cases if (c.get('initial_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['ISR']:.2%} ({sum(1 for c in loop_cases if (c.get('initial_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    logging.info(f"| FSR    | {b_stats['FSR']:.2%} ({sum(1 for c in baseline_cases if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['FSR']:.2%} ({sum(1 for c in loop_cases if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    logging.info(f"| CRSR   | {b_stats['CRSR']:.2%} ({sum(1 for c in [c for c in baseline_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_failing'] if b_stats['n_failing'] else 1}) | "
          f"{l_stats['CRSR']:.2%} ({sum(1 for c in [c for c in loop_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_failing'] if l_stats['n_failing'] else 1}) |")

 
    failure_class_table(baseline_cases, "baseline")
    failure_class_table(loop_cases, "loop")
    logging.info("\nUnrepaired Loop Failure Summary:")
    print_unrepaired_loop_failure_summary(loop_cases);

def load_all_trials(output_dir, num_trials):
    baseline_jsons = []
    loop_jsons = []
    missing_trials = 0
    for i in range(1, num_trials + 1):
        base_path = output_dir / "baseline" / f"trial_{i:02d}" / "run.json"
        loop_path = output_dir / "loop" / f"trial_{i:02d}" / "run.json"
        if not base_path.exists() or not loop_path.exists():
            logging.warning(f"[WARN] Missing results for trial={i}: {base_path} {loop_path}")
            missing_trials += 1
            continue
        with open(base_path, "r") as bf:
            baseline_jsons.append(json.load(bf))
        with open(loop_path, "r") as lf:
            loop_jsons.append(json.load(lf))
    return baseline_jsons, loop_jsons, missing_trials


def extract_trial_num(dirname):
    # Supports trial_01, trial_1, trial_0010, etc.
    m = re.match(r"trial_0*([1-9]\d*|0)$", dirname)
    if m:
        return int(m.group(1))
    return None

def is_baseline_success(baseline_json):
    # Adjust this logic to match *your* definition of baseline success in your JSON!
    return baseline_json.get("TerminalStatus", "") == "success"

def get_first_run_json(trial_path):
    # Your original helper, usually looks for *run.json
    for f in trial_path.glob("*_run.json"):
        return f
    return None


def load_paired_trials(output_dir):

    """
    Loads paired baseline and loop trial JSON objects, matching by trial ID.
    Returns (trial_ids, baseline_jsons, loop_jsons, missing_trials):
        trial_ids: list of matched trial numbers
        baseline_jsons: baseline run dicts (same order as IDs)
        loop_jsons: loop run dicts (same order as IDs)
        missing_trials: count of trials where a loop result was expected but is missing.
    """
    baseline_jsons = []
    loop_jsons = []
    trial_ids = []
    missing_trials = 0

    baseline_dir = output_dir / "baseline"
    loop_dir = output_dir / "loop"

    for trial_path in sorted(list(baseline_dir.glob("trial_*")), key=lambda p: extract_trial_num(p.name) or 0):
        num = extract_trial_num(trial_path.name)
        if num is None:
            continue
        base_file = get_first_run_json(trial_path)
        if not base_file or not base_file.exists():
            continue  # skip trials without valid baseline file

        # Load baseline JSON
        with open(base_file, "r") as bf:
            baseline_json = json.load(bf)

        # Try to find loop result
        loop_trial_path = loop_dir / f"trial_{num:02d}"
        loop_file = get_first_run_json(loop_trial_path)

        if is_baseline_success(baseline_json):
            if loop_file and loop_file.exists():
                with open(loop_file, "r") as lf:
                    loop_json = json.load(lf)
            else:
                # Count all baseline-passing cases as loop-passing too
                loop_json = dict(baseline_json)  # Copies baseline JSON for traceability
                loop_json["CopiedFromBaseline"] = True
                missing_trials += 1
        else:
            if loop_file and loop_file.exists():
                with open(loop_file, "r") as lf:
                    loop_json = json.load(lf)
            else:
                loop_json = {"TerminalStatus": "MISSING_LOOP"}
                missing_trials += 1

        trial_ids.append(num)
        baseline_jsons.append(baseline_json)
        loop_jsons.append(loop_json)

    return trial_ids, baseline_jsons, loop_jsons, missing_trials





def get_failure_class(run_json):
    # Fallback to 'unknown' if no clue
    terminal_status = str(run_json.get("terminal_status", "")).lower()
    # Prefer explicit case_metrics if present
    case_metrics = run_json.get("case_metrics", {})
    if case_metrics and case_metrics.get("initial_failure_classes"):
        return case_metrics.get("initial_failure_classes")
    # Try to propagate known error classes by terminal_status
    elif terminal_status == "parse_error":
        return ["parse_error"]
    elif terminal_status == "semantic_error":
        return ["semantic_error"]
    elif terminal_status == "invariant_violation":
        return ["invariant_violation"]
    elif terminal_status == "tlc_error":
        return ["tlc_error"]
    elif terminal_status == "timeout":
        return ["timeout"]
    elif terminal_status == "skipped":
        return []
    elif terminal_status == "success":
        return []
    elif terminal_status:
        return [terminal_status]
    else:
        return ["unknown"]
    
def extract_case_metrics(baseline_jsons, loop_jsons):
    baseline_cases = []
    loop_cases = []
    all_case_metrics = []
    N = min(len(baseline_jsons), len(loop_jsons))
    for i in range(N):
        trial_case_id = f"trial_{i+1}"
        b = baseline_jsons[i]
        l = loop_jsons[i]
        entry_b = {
            "case_id": trial_case_id,
            "mode": "baseline",
            "initial_status": {"tlc": bool(
                b.get("InitialVerificationSuccess", b.get("initial_verification_success", False))
            )},
            "final_status": {"tlc": _is_tlc_success(b)},
            "TerminalStatus": b.get("TerminalStatus", b.get("terminal_status", "")),
            "initial_failure_classes": get_failure_class(b)
        }
        # Detect baseline-pass / loop-missing or skipped
        loop_terminal = l.get("TerminalStatus", l.get("terminal_status", "")).lower()
        if loop_terminal == "skipped" or (loop_terminal in {"unknown", "missing_loop"} and (b.get("TerminalStatus", b.get("terminal_status", "")).lower() == "success")):
            # If loop is missing/skipped and baseline passed, treat as initial/final TLC pass
            init_tlc = True
            final_tlc = True
        else:
            init_tlc = bool(l.get("InitialVerificationSuccess", l.get("initial_verification_success", False)))
            final_tlc = _is_tlc_success(l)
        entry_l = {
            "case_id": trial_case_id,
            "mode": "loop",
            "initial_status": {"tlc": init_tlc},
            "final_status": {"tlc": final_tlc},
            "TerminalStatus": l.get("TerminalStatus", l.get("terminal_status", "")),
            "initial_failure_classes": get_failure_class(l)
        }

        baseline_cases.append(entry_b)
        loop_cases.append(entry_l)
        all_case_metrics.append(entry_b)
        all_case_metrics.append(entry_l)
    logging.debug("DEBUG: After extract_case_metrics")
    logging.debug("  Baseline final_status tlc: ", [c["final_status"]["tlc"] for c in baseline_cases])
    logging.debug("  Loop final_status tlc: ", [c["final_status"]["tlc"] for c in loop_cases])
    logging.debug("  Baseline TerminalStatus: ", [c.get("TerminalStatus", "") for c in baseline_cases])
    logging.debug("  Loop TerminalStatus: ", [c.get("TerminalStatus", "") for c in loop_cases])
    return baseline_cases, loop_cases, all_case_metrics



def print_unknown_cases(case_metrics_list):
    for entry in case_metrics_list:
        if "unknown" in entry.get("initial_failure_classes", []):
            logging.info(f"Case {entry.get('case_id', '???')} is UNKNOWN. All fields: {entry}")
            logging.info(f"Case {entry.get('case_id', '???')} is UNKNOWN. All fields: {entry}")

def print_unrepaired_loop_failure_summary(case_metrics_list):
    logging.info("| Unrepaired Case | TerminalStatus | Final Failure Classes |")
    logging.info("|----------------|---------------|----------------------|")
    for entry in case_metrics_list:
        if entry.get("mode") == "loop" and not (entry.get("final_status") or {}).get("tlc", True):
            logging.info(f"| {entry.get('case_id','?')} | {entry.get('TerminalStatus','')} | {entry.get('final_failure_classes', entry.get('initial_failure_classes', 'N/A'))} |")


def summarize_full_run(
    root_out,
    task_name,
    baseline_jsons,
    loop_jsons,
    args,
):
    # Make table rows for Markdown/CSV
    rows = []
    num_trials = len(baseline_jsons)
    for i in range(num_trials):
        rows.append(_summarize(baseline_jsons[i], f"baseline_trial_{i+1}"))
        rows.append(_summarize(loop_jsons[i], f"loop_trial_{i+1}"))
    csv_path = root_out / f"comparison_{task_name}.csv"
    md_path = root_out / f"comparison_{task_name}.md"
    _write_csv(csv_path, rows)
    md_table = _to_markdown(rows)

    # Learning efficiency, if requested
    learning_summary = None
    summary_path = None
    if getattr(args, "learning_series", None) or getattr(args, "learning_series_dir", None):
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
            logging.info("No learning-series artifacts found; skipping learning efficiency aggregation.")

    md_path.write_text(md_table + "\n", encoding="utf-8")
    logging.info("Comparison completed.")
    logging.info(f"CSV table:     {csv_path}")
    logging.info(f"Markdown:      {md_path}")
    if learning_summary and summary_path:
        logging.info(f"Learning efficiency summary JSON: {summary_path}")
        logging.info("Learning efficiency summary:")
        logging.info(json.dumps(learning_summary, indent=2))
    logging.info("\n" + md_table)

    logging.debug("len(baseline_jsons):", len(baseline_jsons))
    logging.debug("len(loop_jsons):", len(loop_jsons))

    baseline_cases, loop_cases, all_case_metrics = extract_case_metrics(baseline_jsons, loop_jsons)

    logging.debug("AFTER extract_case_metrics debug:")
    logging.debug("  baseline_cases len:", len(baseline_cases))
    logging.debug("  loop_cases len:", len(loop_cases))

    case_metrics_csv_path = root_out / "case_metrics.csv"
    _write_case_metrics_csv(case_metrics_csv_path, all_case_metrics)

    logging.debug("\n==== DEBUG: baseline_cases ====")
    for c in baseline_cases:
        logging.debug(f"{c['case_id']}: final_status.tlc={c['final_status'].get('tlc')} TerminalStatus={c.get('TerminalStatus', '')} initial_status.tlc={c['initial_status'].get('tlc')}")

    logging.debug("\n==== DEBUG: loop_cases ====")
    for c in loop_cases:
        logging.debug(f"{c['case_id']}: final_status.tlc={c['final_status'].get('tlc')} TerminalStatus={c.get('TerminalStatus', '')} initial_status.tlc={c['initial_status'].get('tlc')}")

    # Side-by-side summaries/stats
    summarize_case_metrics_per_mode(baseline_cases, loop_cases)
    # Timing
    all_llm, all_tlc, all_ovh, all_total = collect_all_timings(baseline_jsons, loop_jsons)
    logging.info("\nTiming statistics per phase (seconds):")
    phases = [
        ("LLM call", all_llm),
        ("TLC call", all_tlc),
        ("Engineering overhead", all_ovh),
        ("Total step", all_total)
    ]
    logging.info("| Phase                | Mean | Median | Min | Max | Attempts |")
    logging.info("|--------------------- |------|--------|-----|-----|----------|")
    for label, data in phases:
        mean_, median_, min_, max_, N_ = timing_stats(data)
        logging.info(f"| {label:<20} | {fmt(mean_)} | {fmt(median_,6)} | {fmt(min_,3)} | {fmt(max_,3)} | {fmt_int(N_,3)} |")
    # McNemar
    mcnemar_analysis(baseline_cases, loop_cases, summary_path=str(root_out / "mcnemar_summary.txt"))
    mcnemar_markdown(baseline_cases, loop_cases, md_path=str(root_out / "mcnemar_summary.md"))
    mcnemar_csv(baseline_cases, loop_cases, csv_path=str(root_out / "mcnemar_summary.csv"))

def main() -> None:
    args = parse_args()
    apply_patch = not args.no_patch
    
    task_path = Path(args.task)
    task = load_task_spec(args.task)
    task_name = (Path(args.task).stem if hasattr(args, "task") else "unknown_task")

    output_dir = Path(args.output_dir)

    with _resolve_module_dir(args, task_path, task) as module_binding:
        validate_module_layout(task, module_binding.root)
        module_dir = module_binding.root

        artifact_root = (
            Path(args.artifact_root)
            if args.artifact_root
            else output_dir.parent / task_name
        )
        root_out = output_dir / task_name
        baseline_out = root_out / "baseline"
        loop_out = root_out / "loop"
        logging.debug("root_out:", root_out)
        logging.debug("baseline_out:", baseline_out)
        logging.debug("loop_out:", loop_out)

        if args.analyze_only:
            trial_ids, baseline_jsons, loop_jsons, missing_trials = load_paired_trials(root_out)
            logging.debug("len(baseline_jsons):", len(baseline_jsons))
            logging.debug("len(loop_jsons):", len(loop_jsons))
            logging.info(f"Loaded {len(trial_ids)} paired trials from {root_out}. Missing loop trials: {missing_trials}")
            summarize_full_run(
                root_out=root_out,
                task_name=task_name,
                baseline_jsons=baseline_jsons,
                loop_jsons=loop_jsons,
                args=args,
            )
            skills_db = None
            skills_json_path = Path('skills.json')
            if skills_json_path.exists():
                with open(skills_json_path, encoding='utf-8') as f:
                    skills_db = json.load(f)
            else:
                print('WARNING: skills.json not found; classification may not be accurate')
                skills_db = []

            reclassify_attempts_with_final_rules(loop_jsons, skills_db, classify_tlc_error)
            logging.debug(f"Analysis-only mode complete. {len(baseline_jsons)} trials analyzed.")
            return

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

            # Always output to task/mode/trial_XX, even for num_trials=1, for full reproducibility/aggregation
            # Determine task name for consistent directory naming
            task_id = getattr(task, "name", None) or getattr(args, "task", None) or "default_task"
            # Use the pattern: results/comparison/<task_name>/baseline/trial_XX/, etc
            baseline_trials_root = root_out / "baseline"
            loop_trials_root = root_out / "loop"
            baseline_trial_out = baseline_trials_root / f"trial_{trial:02d}"
            loop_trial_out = loop_trials_root / f"trial_{trial:02d}"
            baseline_trial_out.mkdir(parents=True, exist_ok=True)
            loop_trial_out.mkdir(parents=True, exist_ok=True)

            events_csv_path = root_out / "repair_and_regression_events.csv"


            # Optionally set seed for reproducibility
            seed = (trial_seed_offset + trial) if trial_seed_offset is not None else None

            modules_baseline = baseline_trial_out / "modules"
            copytree_symlink_safe(module_dir, modules_baseline)

            # Baseline mode
            baseline_provider = build_provider(args.provider, args.model, args.replay_dir)
            baseline_cfg = LoopConfig(
                tla_jar_path=args.tla_jar,
                module_dir=modules_baseline,
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
                apply_patch=apply_patch,
            )
            baseline_json = _load_json(baseline_artifacts["json"])
            baseline_jsons.append(baseline_json)
            baseline_final_status = baseline_json.get("terminal_status", "").lower()

            # Write baseline metrics
            _write_trial_metrics_csv(baseline_trial_out / "metrics.csv", baseline_json, trial, "baseline", seed)


            logging.info(f"Baseline final status: {baseline_final_status}")

            if baseline_final_status == "success":
                logging.info(f"[SKIP LOOP] Baseline already passes in trial {trial}, not running loop experiment.")
                loop_json = {
                    "terminal_status": "skipped",
                    "repair_iterations": 0,
                    "skills_successful": 0,
                    "human_intervention": False,
                    "attempts": [],
                    "case_metrics": {
                        "mode": "loop",
                        "initial_status": {"tlc": True},
                        "final_status": {"tlc": True},
                        "initial_failure_classes": [],
                    }
                }
                loop_jsons.append(loop_json)
                # Write dummy metrics/csv to keep pipeline consistent 
                _write_trial_metrics_csv(loop_trial_out / "metrics.csv", loop_json, trial, "loop", seed)
                continue


            # --- Paired starting spec for loop (NEW: ensure initial spec for loop is the same as baseline) ---
            baseline_initial_spec = str(baseline_trial_out / "modules" / f"{task.module_name}_attempt_1.tla")
            if not os.path.isfile(baseline_initial_spec):
                logging.warning(f"[WARN] Baseline initial spec not found: {baseline_initial_spec}")

            # Loop mode with regression tracking
            modules_loop = loop_trial_out / "modules"
            copytree_symlink_safe(module_dir, modules_loop)
            loop_provider = build_provider(args.provider, args.model, args.replay_dir)
            loop_cfg = LoopConfig(
                tla_jar_path=args.tla_jar,
                module_dir=modules_loop,
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
                apply_patch=apply_patch,
                initial_spec_override=baseline_initial_spec,  # <<--- key change: paired initial spec
            )
            loop_json = _load_json(loop_artifacts["json"])

            # --- Step 2: Regression tracking ---
            # Track TLC status sequence for this trial
            regression_flag = False
            regression_attempt_index = None
            tlc_statuses = []
            for attempt in loop_json.get("attempts", []):
                tlc_statuses.append(attempt.get("status", ""))
            # Regression: TLC success followed by any later non-success
            seen_success = False
            for idx, status in enumerate(tlc_statuses):
                if status == "success":
                    seen_success = True
                elif seen_success and status != "success":
                    regression_flag = True
                    regression_attempt_index = idx + 1  # 1-based for user
                    logging.info(f"[REGRESSION] Trial {trial}: Regression detected at attempt {regression_attempt_index}. Status sequence: {tlc_statuses}")
                    _log_event_to_csv(events_csv_path, trial, "regression", regression_attempt_index, "loop", {"tlc_statuses": tlc_statuses})
                    break
            loop_json["regression"] = regression_flag

            # Early stop (checkpoint gating) already handled in run_experiment
            loop_jsons.append(loop_json)

            # Write loop metrics
            _write_trial_metrics_csv(loop_trial_out / "metrics.csv", loop_json, trial, "loop", seed)

            # --- Step 3: Repair event logging (paired with baseline) ---
            # Repair: baseline fails, loop succeeds
            baseline_final_status = baseline_json.get("terminal_status", "")
            loop_final_status = loop_json.get("terminal_status", "")
            if (str(baseline_final_status).lower() != "success" and str(loop_final_status).lower() == "success"):
                # Find first attempt in loop_json where status == 'success'
                attempts = loop_json.get("attempts", [])
                repair_attempt_index = None
                for idx, attempt in enumerate(attempts):
                    if attempt.get("status", "") == "success":
                        repair_attempt_index = idx + 1  # 1-based counting
                        logging.info(f"[REPAIR] Trial {trial}: Repair detected at attempt {repair_attempt_index}.")
                        _log_event_to_csv(events_csv_path, trial, "repair", repair_attempt_index, "loop", {
                            "attempt": attempt,
                            "baseline_terminal_status": baseline_final_status,
                            "loop_terminal_status": loop_final_status
                        })
                        break

        summarize_full_run(
            root_out=root_out,
            task_name=task_name,
            baseline_jsons=baseline_jsons,
            loop_jsons=loop_jsons,
            args=args,
        )

if __name__ == "__main__":
    main()
