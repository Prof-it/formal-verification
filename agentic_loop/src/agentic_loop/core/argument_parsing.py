"""Argument parsing for CLI tools (refactored).
Extracted from legacy compare_cli.py.
"""

import argparse

def parse_args() -> argparse.Namespace:
    """Argument parser for agentic_loop compare CLI (refactored from legacy)."""
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