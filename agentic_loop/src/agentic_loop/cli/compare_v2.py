"""
compare_v2.py — New CLI entrypoint for agentic_loop (refactored).
This file uses only the new modules.
"""

from agentic_loop.core.argument_parsing import parse_args
from agentic_loop.metrics.metrics_io import write_csv, to_markdown
from agentic_loop.metrics.learning_efficiency import compute_learning_efficiency
from agentic_loop.metrics.case_metrics_analysis import summarize_case_metrics, summarize_case_metrics_per_mode
from agentic_loop.metrics.stats_analysis import mcnemar_analysis, mcnemar_markdown, mcnemar_csv
from agentic_loop.utils.timing_utils import timing_stats, fmt, fmt_int

def main():
    args = parse_args()
    print("Parsed arguments:", vars(args))

    # Now demo an empty table for metrics_io/markdown
    headers_row = [{
        "Mode": "demo",
        "TerminalStatus": "dummy",
        "Attempts": 0,
        "ParseSuccessRate": "0.000",
        "SemanticSuccessRate": "0.000",
        "GenerationSuccess": 0,
        "InitialVerificationSuccess": 0,
        "VerificationGap": 0,
        "RepairSuccess": 0,
        "RepairIterations": 0,
        "CounterexamplesSeen": 0,
        "CounterexamplesResolved": 0,
        "SkillsApplied": 0,
        "SkillsSuccessful": 0,
        "HumanIntervention": 0,
        "FinalParseOK": False,
        "FinalSemanticOK": False,
        "FinalInvariantViolation": False,
        "TotalErrors": 0
    }]
    print("\nMarkdown Table Example:")
    print(to_markdown(headers_row))

    # Timing utility test
    print("\nTiming stats example (empty):", timing_stats([]))
    print("Timing stats example ([1,2,3,4]):", timing_stats([1,2,3,4]))

    # Learning efficiency dummy test
    print("\nLearning efficiency example:", compute_learning_efficiency([]))

    # Case analysis print test (should work but trivial for empty input)
    summarize_case_metrics([])
    summarize_case_metrics_per_mode([], [])

if __name__ == "__main__":
    main()