
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
import numpy as np
from statsmodels.stats.contingency_tables import mcnemar
from .task_loader import load_task_spec

from collections import Counter

import os
import glob
import tempfile


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
        warnings.warn(
            f"Refusing to recursively stage/copy project root directory '{project_root}' (source: '{stage_source}') for task '{task_spec.name}'."
        )
        return None

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

    # If no module directory is found or mapped, create a fresh temp dir and let the bootstrap take over
    import tempfile
    fresh_moduledir = Path(tempfile.mkdtemp(prefix=f"{task_spec.name}_", dir=str(module_root.resolve())))
    print(f"[Bootstrap-Module] No input module-dir given; created temp dir: {fresh_moduledir}")
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

def _write_case_metrics_csv(csv_path, case_metrics_list):
    """
    Writes out a CSV summarizing per-case/canonical metrics for every run
    """
    keys = [
        "case_id", "mode", "initial_candidate", "initial_status", "final_status",
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


def _summarize_case_metrics(case_metrics_list):
    """
    Print overall metrics such as CRSR, ISR, FSR and failure-class repairability.
    """
    n_total = len(case_metrics_list)
    # Use dicts directly, not json.loads()
    isr = sum(1 for c in case_metrics_list if (c.get("initial_status") or {}).get("tlc")) / n_total if n_total else 0
    fsr = sum(1 for c in case_metrics_list if (c.get("final_status") or {}).get("tlc")) / n_total if n_total else 0
    failing = [c for c in case_metrics_list if not (c.get("initial_status") or {}).get("tlc")]
    n_failing = len(failing)
    crsr = sum(1 for c in failing if (c.get("final_status") or {}).get("tlc")) / n_failing if n_failing else 0
    print(f"Initial TLC Success Rate (ISR): {isr:.2%} ({sum(1 for c in case_metrics_list if (c.get('initial_status') or {}).get('tlc'))}/{n_total})")
    print(f"Final TLC Success Rate (FSR): {fsr:.2%} ({sum(1 for c in case_metrics_list if (c.get('final_status') or {}).get('tlc'))}/{n_total})")
    print(f"Conditional Repair Success Rate (CRSR): {crsr:.2%} ({sum(1 for c in failing if (c.get('final_status') or {}).get('tlc'))}/{n_failing if n_failing else 1})")
    # Failure class repairability table
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
    print("\n| Failure class | Cases | Repaired | Repairability |")
    print("|--------------|-------|----------|--------------|")
    for fc, val in sorted(fc_table.items()):
        total = val["total"]
        repaired = val["repaired"]
        print(f"| {fc} | {total} | {repaired} | {repaired/total:.1%} |")

def mcnemar_analysis(case_metrics_list, summary_path="mcnemar_summary.txt"):
    from collections import Counter
    mcnemar, binom_test = None, None
    try:
        from statsmodels.stats.contingency_tables import mcnemar
    except ImportError:
        mcnemar = None
    try:
        from scipy.stats import binom_test
    except ImportError:
        binom_test = None

    before_after = []
    for c in case_metrics_list:
        ini = bool((c.get("initial_status") or {}).get("tlc", False))
        fin = bool((c.get("final_status") or {}).get("tlc", False))
        before_after.append((ini, fin))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]   # Fail→Pass
    PF = counts[(True, False)]   # Pass→Fail
    PP = counts[(True, True)]
    n = FF + FP + PF + PP

    lines = []
    lines.append("\nPaired TLC outcomes:\n")
    lines.append("Initial TLC  | After TLC Fail | After TLC Pass |\n")
    lines.append("-------------|----------------|---------------|\n")
    lines.append(f"Fail         |   {FF:<14d}| {FP:<14d}|\n")
    lines.append(f"Pass         |   {PF:<14d}| {PP:<14d}|\n")

    lines.append(f"\nMcNemar's test on discordant pairs (Fail→Pass={FP}, Pass→Fail={PF})\n")
    if mcnemar is not None:
        table = [[FF, FP], [PF, PP]]
        result = mcnemar(table, exact=True)
        pval = None
        # Try all known ways to get a p-value
        if hasattr(result, "pvalue"):
            pval = getattr(result, "pvalue")
        elif hasattr(result, "__dict__") and "pvalue" in result.__dict__:
            pval = result.__dict__["pvalue"]
        elif isinstance(result, dict) and "pvalue" in result:
            pval = result["pvalue"]
        if pval is not None:
            lines.append(f"McNemar p-value: {pval:.3g}\n")
        elif binom_test is not None:
            # Safe to access here!
            b = FP
            c = PF
            discordant = b + c
            if discordant > 0:
                p = 2 * binom_test(min(b, c), n=discordant, p=0.5, alternative='two-sided')
                lines.append(f"Binomial p-value (McNemar fallback): {p:.3g}\n")
            else:
                lines.append("Binomial test not applicable (no discordant pairs).\n")
        else:
            # Manual fallback: binomial p-value calculation for McNemar test (two-tailed) at p=0.5, only standard library.
            import math
            def binom_coeff(n, k):
                return math.comb(n, k)
            b = FP
            c = PF
            discordant = b + c
            if discordant > 0:
                k = min(b, c)
                # Two-sided: sum prob(X <= k) * 2 (for symmetry at p=0.5)
                prob = sum(binom_coeff(discordant, i) * (0.5 ** discordant) for i in range(0, k+1))
                p_conservative = 2 * prob
                lines.append(f"Approximate binomial (no-scipy) p-value: {p_conservative:.3g}\n")
            else:
                lines.append("No discordant pairs: cannot compute binomial p-value.\n")

    elif binom_test is not None:
        b = FP
        c = PF
        discordant = b + c
        if discordant > 0:
            p = 2 * binom_test(min(b, c), n=discordant, p=0.5, alternative='two-sided')
            lines.append(f"Binomial p-value (McNemar fallback): {p:.3g}\n")
        else:
            lines.append("Binomial test not applicable (no discordant pairs).\n")
    else:
        lines.append("Install statsmodels or scipy for p-value.\n")


    # Extra insight
    lines.append(f"Baseline TLC pass rate: {(PF+PP)/n:.1%}\n")
    lines.append(f"Loop TLC pass rate:     {(FP+PP)/n:.1%}\n")

    summary_text = "".join(lines)
    print(summary_text)
    with open(summary_path, "w", encoding="utf-8") as out_f:
        out_f.write(summary_text)
    print(f"\n==> McNemar summary written to {summary_path}")


def mcnemar_markdown(case_metrics_list, md_path="mcnemar_summary.md"):

    before_after = []
    for c in case_metrics_list:
        ini = bool((c.get("initial_status") or {}).get("tlc", False))
        fin = bool((c.get("final_status") or {}).get("tlc", False))
        before_after.append((ini, fin))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]
    PF = counts[(True, False)]
    PP = counts[(True, True)]
    table = f"""
|                | After TLC Fail | After TLC Pass |
|:---------------|:--------------|:--------------|
| Before: Fail   | {FF}           | {FP}           |
| Before: Pass   | {PF}           | {PP}           |
"""
    result = mcnemar([[FF, FP],[PF, PP]], exact=True)
    md = (
        "# Paired TLC outcome table (for McNemar's test)\n"
        f"{table}\n"
        f"McNemar p-value: {result.pvalue:.3g}\n"
        f"Conditional repair success: {FP}/({FF+FP}) = {(FP/(FF+FP) if (FF+FP)>0 else 0):.1%}\n"
        f"Baseline TLC pass rate: {(PF+PP)/(FF+FP+PF+PP):.1%}\n"
        f"Loop TLC pass rate:     {(FP+PP)/(FF+FP+PF+PP):.1%}\n"
    )
    with open(md_path, "w", encoding="utf-8") as out_f:
        out_f.write(md)
    print(f"McNemar summary written to {md_path}")

def mcnemar_csv(case_metrics_list, csv_path="mcnemar_summary.csv"):
    before_after = []
    for c in case_metrics_list:
        ini = bool((c.get("initial_status") or {}).get("tlc", False))
        fin = bool((c.get("final_status") or {}).get("tlc", False))
        before_after.append((ini, fin))
    counts = Counter(before_after)
    FF = counts[(False, False)]
    FP = counts[(False, True)]
    PF = counts[(True, False)]
    PP = counts[(True, True)]
    with open(csv_path, "w", newline='', encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["", "After TLC Fail", "After TLC Pass"])
        writer.writerow(["Before: Fail", FF, FP])
        writer.writerow(["Before: Pass", PF, PP])
    print(f"McNemar table written to {csv_path}")

# Gather all per-attempt timings from both modes
def collect_all_timings(baseline_jsons, loop_jsons):
    all_llm = []
    all_tlc = []
    all_ovh = []
    all_total = []
    all_runs = baseline_jsons + loop_jsons
    for run in all_runs:
        for attempt in run.get("attempts", []):
            timing = attempt.get("timing", {})
            # Only include attempts where timing is present and non-empty
            if timing and "duration_llm" in timing:
                all_llm.append(float(timing.get("duration_llm", 0)))
                all_tlc.append(float(timing.get("duration_tlc", 0)))
                all_ovh.append(float(timing.get("duration_engineering_overhead", 0)))
                all_total.append(float(timing.get("duration_total", 0)))
    return all_llm, all_tlc, all_ovh, all_total

def timing_stats(times):
    if not times:
        return ("—", "—", "—", "—", 0)
    return (
        round(float(np.mean(times)), 2),
        round(float(np.median(times)), 2),
        round(float(np.min(times)), 2),
        round(float(np.max(times)), 2),
        len(times)
    )
def fmt(v, width=5):
    if isinstance(v, (int, float)):
        return f"{v:>{width}.2f}"
    return f"{v:>{width}}"

def fmt_int(v, width=3):
    if isinstance(v, int):
        return f"{v:>{width}d}"
    return f"{v:>{width}}"

def copytree_symlink_safe(src, dst):
    # Recursively copy a directory tree (src) into new location (dst)
    # Overwrites dst if exists; skips symlinks for extra safety.
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(src, dst, symlinks=False, dirs_exist_ok=True)
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
        print(f"\n| Failure class ({label}) | Cases | Repaired | Repairability |")
        print("|----------------------|-------|----------|--------------|")
        for fc, val in sorted(fc_table.items()):
            total = val["total"]
            repaired = val["repaired"]
            rep_rate = (repaired/total)*100 if total > 0 else 0
            print(f"| {fc} | {total} | {repaired} | {rep_rate:.1f}% |")

def summarize_case_metrics_per_mode(baseline_cases, loop_cases):
    """
    Print ISR/FSR/CRSR/failure-class repairability per mode side-by-side.
    """
    import json
    # Helper for stats extraction
    def extract_stats(cases):
        n_total = len(cases)
        isr = sum(1 for c in cases if (c.get("initial_status") or {}).get("tlc")) / n_total if n_total else 0
        fsr = sum(1 for c in cases if (c.get("final_status") or {}).get("tlc")) / n_total if n_total else 0
        failing = [c for c in cases if not (c.get("initial_status") or {}).get("tlc")]
        n_failing = len(failing)
        crsr = sum(1 for c in failing if (c.get("final_status") or {}).get("tlc")) / n_failing if n_failing else 0
        return dict(ISR=isr, FSR=fsr, CRSR=crsr, n_total=n_total, n_failing=n_failing)
    b_stats = extract_stats(baseline_cases)
    l_stats = extract_stats(loop_cases)

    print("\nSuccess Rate Comparison (per mode):")
    print("| Metric | Baseline | Loop |")
    print("|--------|----------|------|")
    print(f"| ISR    | {b_stats['ISR']:.2%} ({sum(1 for c in baseline_cases if (c.get('initial_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['ISR']:.2%} ({sum(1 for c in loop_cases if (c.get('initial_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    print(f"| FSR    | {b_stats['FSR']:.2%} ({sum(1 for c in baseline_cases if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_total']}) | "
          f"{l_stats['FSR']:.2%} ({sum(1 for c in loop_cases if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_total']}) |")
    print(f"| CRSR   | {b_stats['CRSR']:.2%} ({sum(1 for c in [c for c in baseline_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{b_stats['n_failing'] if b_stats['n_failing'] else 1}) | "
          f"{l_stats['CRSR']:.2%} ({sum(1 for c in [c for c in loop_cases if not (c.get('initial_status') or {}).get('tlc')] if (c.get('final_status') or {}).get('tlc'))}/{l_stats['n_failing'] if l_stats['n_failing'] else 1}) |")

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
        print(f"\n| Failure class ({label}) | Cases | Repaired | Repairability |")
        print("|----------------------|-------|----------|--------------|")
        for fc, val in sorted(fc_table.items()):
            total = val["total"]
            repaired = val["repaired"]
            rep_rate = (repaired/total)*100 if total > 0 else 0
            print(f"| {fc} | {total} | {repaired} | {rep_rate:.1f}% |")
    failure_class_table(baseline_cases, "baseline")
    failure_class_table(loop_cases, "loop")

def main() -> None:
    args = parse_args()
    apply_patch = not args.no_patch

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


            # Write baseline metrics
            _write_trial_metrics_csv(baseline_trial_out / "metrics.csv", baseline_json, trial, "baseline", seed)


            # Loop mode with regression tracking
            # Loop -- per-trial input copy
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
            )
            loop_json = _load_json(loop_artifacts["json"])

            # --- Step 2: Regression tracking ---
            # Track TLC status sequence for this trial
            regression_flag = False
            tlc_statuses = []
            for attempt in loop_json.get("attempts", []):
                tlc_statuses.append(attempt.get("status", ""))
            # Regression: TLC success followed by any later non-success
            seen_success = False
            for status in tlc_statuses:
                if status == "success":
                    seen_success = True
                elif seen_success and status != "success":
                    regression_flag = True
                    break
            loop_json["regression"] = regression_flag
            # Early stop (checkpoint gating) already handled in run_experiment
            loop_jsons.append(loop_json)

            # Write loop metrics
            _write_trial_metrics_csv(loop_trial_out / "metrics.csv", loop_json, trial, "loop", seed)

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

        all_case_metrics = []
        for j in range(num_trials):
            all_case_metrics.append(baseline_jsons[j].get("case_metrics", {}))
            all_case_metrics.append(loop_jsons[j].get("case_metrics", {}))
        csv_path = root_out / "case_metrics.csv"
        _write_case_metrics_csv(csv_path, all_case_metrics)
        _summarize_case_metrics(all_case_metrics)


        all_case_metrics = []
        baseline_cases = []
        loop_cases = []
        for j in range(num_trials):
            # Baseline
            b = baseline_jsons[j]
            b_case_metrics = b.get("case_metrics", {})
            entry_b = {
                "mode": "baseline",
                "initial_status": {"tlc": bool(
                    b.get("InitialVerificationSuccess", b.get("initial_verification_success", False))
                )},
                "final_status": {"tlc": bool(
                    b.get("TerminalStatus", b.get("terminal_status", "")) == "success"
                )},
                "initial_failure_classes": b_case_metrics.get("initial_failure_classes", [])
            }
            all_case_metrics.append(entry_b)
            baseline_cases.append(entry_b)

            # Loop
            l = loop_jsons[j]
            l_case_metrics = l.get("case_metrics", {})
            entry_l = {
                "mode": "loop",
                "initial_status": {"tlc": bool(
                    l.get("InitialVerificationSuccess", l.get("initial_verification_success", False))
                )},
                "final_status": {"tlc": bool(
                    l.get("TerminalStatus", l.get("terminal_status", "")) == "success"
                )},
                "initial_failure_classes": l_case_metrics.get("initial_failure_classes", [])
            }
            loop_cases.append(entry_l)


        csv_path = root_out / "case_metrics.csv"
        _write_case_metrics_csv(csv_path, all_case_metrics)

        # New summary: print separate and side-by-side aggregated stats per mode
        summarize_case_metrics_per_mode(baseline_cases, loop_cases)


        all_llm, all_tlc, all_ovh, all_total = collect_all_timings(baseline_jsons, loop_jsons)

        print("\nTiming statistics per phase (seconds):")
        phases = [
            ("LLM call", all_llm),
            ("TLC call", all_tlc),
            ("Engineering overhead", all_ovh),
            ("Total step", all_total)
        ]
        print("| Phase                | Mean | Median | Min | Max | Attempts |")
        print("|--------------------- |------|--------|-----|-----|----------|")

        for label, data in phases:
            mean_, median_, min_, max_, N_ = timing_stats(data)
            print(f"| {label:<20} | {fmt(mean_)} | {fmt(median_,6)} | {fmt(min_,3)} | {fmt(max_,3)} | {fmt_int(N_,3)} |")

        mcnemar_analysis(all_case_metrics, summary_path=str(root_out / "mcnemar_summary.txt"))
        mcnemar_markdown(all_case_metrics, md_path=str(root_out / "mcnemar_summary.md"))
        mcnemar_csv(all_case_metrics, csv_path=str(root_out / "mcnemar_summary.csv"))

if __name__ == "__main__":
    main()
