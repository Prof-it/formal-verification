from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Dict, List

from .engine import run_experiment
from .models import LoopConfig
from .providers import build_provider


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run baseline and loop modes on one task and generate a consolidated table"
    )
    parser.add_argument("--task", required=True, help="Path to task YAML")
    parser.add_argument("--tla-jar", required=True, help="Path to tla2tools.jar")
    parser.add_argument("--module-dir", required=True, help="Directory containing .tla and .cfg files")
    parser.add_argument("--output-dir", required=True, help="Directory for comparison outputs")
    parser.add_argument("--prompts-dir", default="prompts", help="Prompt template directory")
    parser.add_argument("--prompt-mode", choices=["zero_shot", "one_shot"], default="one_shot")
    parser.add_argument("--max-iterations", type=int, default=3)
    parser.add_argument("--timeout-seconds", type=int, default=180)

    parser.add_argument("--provider", choices=["replay", "openai"], default="replay")
    parser.add_argument("--model", default="gpt-5")
    parser.add_argument("--replay-dir", default=None)
    return parser.parse_args()


def _load_json(path: str) -> Dict[str, Any]:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _summarize(run_json: Dict[str, Any], mode: str) -> Dict[str, Any]:
    attempts: List[Dict[str, Any]] = run_json.get("attempts", [])
    last = attempts[-1] if attempts else {}

    return {
        "Mode": mode,
        "TerminalStatus": run_json.get("terminal_status", "unknown"),
        "Attempts": len(attempts),
        "ParseSuccessRate": f"{run_json.get('parse_success_rate', 0.0):.3f}",
        "SemanticSuccessRate": f"{run_json.get('semantic_success_rate', 0.0):.3f}",
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
        "| Mode | TerminalStatus | Attempts | ParseSuccessRate | SemanticSuccessRate | "
        "FinalParseOK | FinalSemanticOK | FinalInvariantViolation | TotalErrors |"
    )
    divider = "|---|---|---:|---:|---:|---|---|---|---:|"
    lines = [header, divider]
    for row in rows:
        lines.append(
            "| {Mode} | {TerminalStatus} | {Attempts} | {ParseSuccessRate} | {SemanticSuccessRate} | "
            "{FinalParseOK} | {FinalSemanticOK} | {FinalInvariantViolation} | {TotalErrors} |".format(**row)
        )
    return "\n".join(lines)


def main() -> None:
    args = parse_args()

    from .task_loader import load_task_spec

    task = load_task_spec(args.task)

    root_out = Path(args.output_dir)
    baseline_out = root_out / "baseline"
    loop_out = root_out / "loop"
    baseline_out.mkdir(parents=True, exist_ok=True)
    loop_out.mkdir(parents=True, exist_ok=True)

    baseline_provider = build_provider(args.provider, args.model, args.replay_dir)
    baseline_cfg = LoopConfig(
        tla_jar_path=args.tla_jar,
        module_dir=args.module_dir,
        output_dir=str(baseline_out),
        prompt_mode=args.prompt_mode,
        max_iterations=args.max_iterations,
        timeout_seconds=args.timeout_seconds,
    )
    baseline_artifacts = run_experiment(
        task=task,
        config=baseline_cfg,
        prompts_dir=args.prompts_dir,
        provider=baseline_provider,
        mode="baseline",
    )

    loop_provider = build_provider(args.provider, args.model, args.replay_dir)
    loop_cfg = LoopConfig(
        tla_jar_path=args.tla_jar,
        module_dir=args.module_dir,
        output_dir=str(loop_out),
        prompt_mode=args.prompt_mode,
        max_iterations=args.max_iterations,
        timeout_seconds=args.timeout_seconds,
    )
    loop_artifacts = run_experiment(
        task=task,
        config=loop_cfg,
        prompts_dir=args.prompts_dir,
        provider=loop_provider,
        mode="loop",
    )

    baseline_json = _load_json(baseline_artifacts["json"])
    loop_json = _load_json(loop_artifacts["json"])

    rows = [_summarize(baseline_json, "baseline"), _summarize(loop_json, "loop")]

    csv_path = root_out / f"comparison_{task.name}.csv"
    md_path = root_out / f"comparison_{task.name}.md"
    _write_csv(csv_path, rows)
    md_table = _to_markdown(rows)
    md_path.write_text(md_table + "\n", encoding="utf-8")

    print("Comparison completed.")
    print(f"Baseline JSON: {baseline_artifacts['json']}")
    print(f"Loop JSON:     {loop_artifacts['json']}")
    print(f"CSV table:     {csv_path}")
    print(f"Markdown:      {md_path}")
    print("\n" + md_table)


if __name__ == "__main__":
    main()
