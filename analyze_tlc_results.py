#!/usr/bin/env python3
"""
TLC Validation Analysis Tool for Neural-Symbolic Verification Paper
Processes TLC results and generates publication-ready tables and charts.
"""

import csv
import json
import os
import sys
from pathlib import Path
from datetime import datetime

def load_results(csv_path):
    """Load TLC results from CSV"""
    results = []
    if not Path(csv_path).exists():
        print(f"Error: Results file not found: {csv_path}")
        return results
    
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            results.append(row)
    return results

def generate_summary_table(results):
    """Generate summary table for paper"""
    print("\n" + "="*100)
    print("EMPIRICAL TLC VALIDATION RESULTS")
    print("="*100)
    print(f"\nGenerated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    
    # Header
    print(
        f"{'Scenario':<30} {'Status':<20} {'States':<15} {'Depth':<10} "
        f"{'Mean(ms)':<12} {'CI95(±ms)':<12} {'Violations':<12}"
    )
    print("-" * 100)
    
    for row in results:
        if row['Scenario'] == 'Scenario':  # Skip header row
            continue

        mean_ms = row.get('MeanWallTime(ms)', row.get('WallTime(ms)', 'N/A'))
        ci95 = row.get('CI95HalfWidth(ms)', 'N/A')

        print(f"{row['Scenario']:<30} "
              f"{row['Status']:<20} "
              f"{row['TotalStates']:<15} "
              f"{row['Depth']:<10} "
              f"{mean_ms:<12} "
              f"{ci95:<12} "
              f"{row['ViolationsFound']:<12}")
    
    print("-" * 100)

def generate_latex_table(results):
    """Generate LaTeX table for paper"""
    print("\n" + "="*100)
    print("LATEX TABLE FOR PAPER")
    print("="*100 + "\n")
    
    latex_lines = [
        "\\begin{table}[h!]",
        "\\centering",
        "\\caption{TLC Model Checking Results for Refinement Validation}",
        "\\label{tab:tlc-results}",
        "\\begin{tabular}{|l|c|r|c|r|r|c|}",
        "\\hline",
        "\\textbf{Scenario} & \\textbf{Status} & \\textbf{States} & \\textbf{Depth} & \\textbf{Mean (ms)} & \\textbf{95\\% CI (±ms)} & \\textbf{Violations} \\\\",
        "\\hline"
    ]
    
    for row in results:
        if row['Scenario'] == 'Scenario':
            continue
        
        status_tex = "\\checkmark" if row['Status'] == 'COMPLETE' else "\\times"
        violations_tex = "Yes" if row['ViolationsFound'] == "Yes" else "No"
        mean_ms = row.get('MeanWallTime(ms)', row.get('WallTime(ms)', 'N/A'))
        ci95 = row.get('CI95HalfWidth(ms)', 'N/A')
        
        latex_lines.append(
            f"{row['Scenario']:<30} & {status_tex} & "
            f"{row['TotalStates']:<10} & {row['Depth']:<8} & "
            f"{mean_ms:<12} & {ci95:<12} & {violations_tex} \\\\" 
        )
    
    latex_lines.extend([
        "\\hline",
        "\\end{tabular}",
        "\\end{table}"
    ])
    
    for line in latex_lines:
        print(line)

def to_float(value, default=0.0):
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def to_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def analyze_scenarios(results):
    """Provide generic insights for any TLC scenario set"""
    print("\n" + "="*100)
    print("ANALYSIS AND INSIGHTS")
    print("="*100 + "\n")

    rows = [row for row in results if row.get('Scenario') and row['Scenario'] != 'Scenario']
    if not rows:
        print("No scenario rows found in results.")
        return

    total = len(rows)
    complete_count = sum(1 for row in rows if row.get('Status') == 'COMPLETE')
    violation_count = sum(1 for row in rows if row.get('ViolationsFound') == 'Yes')
    failure_count = sum(1 for row in rows if row.get('Status') not in ('COMPLETE', 'VIOLATIONS_FOUND'))

    print(f"Scenarios evaluated: {total}")
    print(f"Completed without TLC errors: {complete_count}")
    print(f"Scenarios with property/invariant violations: {violation_count}")
    print(f"Scenarios with execution/config failures: {failure_count}")

    largest = max(rows, key=lambda row: to_int(row.get('TotalStates', '0')))
    slowest = max(rows, key=lambda row: to_float(row.get('MeanWallTime(ms)', row.get('WallTime(ms)', '0'))))

    largest_states = to_int(largest.get('TotalStates', '0'))
    slowest_mean = to_float(slowest.get('MeanWallTime(ms)', slowest.get('WallTime(ms)', '0')))
    slowest_ci95 = slowest.get('CI95HalfWidth(ms)', 'N/A')

    print("\nLargest explored state space:")
    print(f"  - Scenario: {largest.get('Scenario', 'N/A')}")
    print(f"  - States: {largest_states}")

    print("\nSlowest mean runtime:")
    print(f"  - Scenario: {slowest.get('Scenario', 'N/A')}")
    print(f"  - Mean time: {slowest_mean:.2f} ms")
    print(f"  - 95% CI half-width: ±{slowest_ci95} ms")

def generate_json_report(results, output_path):
    """Generate machine-readable JSON report"""
    json_data = {
        "title": "TLC Validation Results for Neural-Symbolic Verification",
        "generated": datetime.now().isoformat(),
        "scenarios": []
    }
    
    for row in results:
        if row['Scenario'] != 'Scenario':
            mean_ms_raw = row.get('MeanWallTime(ms)', row.get('WallTime(ms)', '0'))
            ci95_raw = row.get('CI95HalfWidth(ms)', '0')
            json_data["scenarios"].append({
                "name": row['Scenario'],
                "config": row['Configuration'],
                "status": row['Status'],
                "states": row['TotalStates'],
                "depth": row['Depth'],
                "time_milliseconds_mean": float(mean_ms_raw) if mean_ms_raw != 'N/A' else 0.0,
                "time_milliseconds_ci95_half_width": float(ci95_raw) if ci95_raw != 'N/A' else 0.0,
                "violations": row['ViolationsFound']
            })
    
    with open(output_path, 'w') as f:
        json.dump(json_data, f, indent=2)
    
    print(f"\nJSON report saved to: {output_path}")

def main():
    script_dir = Path(__file__).resolve().parent

    if len(sys.argv) > 1:
        csv_file = Path(sys.argv[1]).expanduser().resolve()
        results_dir = csv_file.parent
    else:
        results_dir = Path(os.environ.get("RESULTS_DIR", str(script_dir / "results"))).expanduser().resolve()
        csv_file = Path(os.environ.get("RESULTS_CSV", str(results_dir / "tlc_results.csv"))).expanduser().resolve()
    
    results = load_results(str(csv_file))
    
    if not results:
        print("No results to analyze. Run the TLC validation script first:")
        print("  ./run_tlc_validation.sh")
        return
    
    # Generate outputs
    generate_summary_table(results)
    generate_latex_table(results)
    analyze_scenarios(results)
    
    # Generate JSON report
    json_report = results_dir / "tlc_results.json"
    generate_json_report(results, str(json_report))
    
    print(f"\n{'='*100}")
    print("Analysis complete. Results files generated in:", results_dir)
    print(f"{'='*100}\n")

if __name__ == "__main__":
    main()
