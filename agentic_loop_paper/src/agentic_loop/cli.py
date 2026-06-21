from __future__ import annotations

import argparse
from pathlib import Path

from .engine import run_experiment
from .models import LoopConfig
from .providers import build_provider


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Agentic loop runner for NL-to-TLA experiments")
    parser.add_argument("--task", required=True, help="Path to task YAML")
    parser.add_argument("--tla-jar", required=True, help="Path to tla2tools.jar")
    parser.add_argument("--module-dir", required=True, help="Directory containing .tla and .cfg files")
    parser.add_argument("--output-dir", required=True, help="Directory to store run artifacts")
    parser.add_argument("--prompts-dir", default="prompts", help="Prompt template directory")
    parser.add_argument("--mode", choices=["baseline", "loop"], default="loop")
    parser.add_argument("--prompt-mode", choices=["zero_shot", "one_shot"], default="one_shot")
    parser.add_argument("--max-iterations", type=int, default=3)
    parser.add_argument("--timeout-seconds", type=int, default=180)

    parser.add_argument("--provider", choices=["replay", "openai"], default="replay")
    parser.add_argument("--model", default="gpt-5")
    parser.add_argument("--replay-dir", default=None)
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    from .task_loader import load_task_spec

    task = load_task_spec(args.task)
    provider = build_provider(args.provider, args.model, args.replay_dir)

    config = LoopConfig(
        tla_jar_path=args.tla_jar,
        module_dir=args.module_dir,
        output_dir=args.output_dir,
        prompt_mode=args.prompt_mode,
        max_iterations=args.max_iterations,
        timeout_seconds=args.timeout_seconds,
    )

    artifact_paths = run_experiment(
        task=task,
        config=config,
        prompts_dir=args.prompts_dir,
        provider=provider,
        mode=args.mode,
    )

    print("Run completed.")
    print(f"JSON: {artifact_paths['json']}")
    print(f"CSV:  {artifact_paths['csv']}")


if __name__ == "__main__":
    main()
