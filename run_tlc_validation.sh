#!/bin/bash

# Empirical TLC validation harness
# Reusable across subprojects by configuring MODULE_DIR, MODULE_NAME, and SCENARIOS.

set -e

RUNS_PER_SCENARIO=3
RUN_MILLION_SCALE=${RUN_MILLION_SCALE:-0}
RUN_BREAKDOWN_WITNESS=${RUN_BREAKDOWN_WITNESS:-0}
SLEEP_BETWEEN_SCENARIOS=${SLEEP_BETWEEN_SCENARIOS:-2}

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="${MODULE_DIR:-${ROOT_DIR}/tla_modules}"
MODULE_NAME="${MODULE_NAME:-MainCheck}"
TLA_JAR_PATH="${TLA_JAR_PATH:-${PROJECT_DIR}/tla2tools.jar}"
TLC_STOP_AFTER_SECONDS="${TLC_STOP_AFTER_SECONDS:-3600}"
OUTPUT_DIR="${RESULTS_DIR:-${ROOT_DIR}/results}"
RESULTS_CSV="${OUTPUT_DIR}/tlc_results.csv"
TIMESTAMP=$(date +"%Y-%m-%d_%H-%M-%S")

DEFAULT_SCENARIOS="Scenario1_Strict:MainCheck_Strict.cfg;Scenario2_NoUniqueness:MainCheck_NoUniqueness.cfg;Scenario3_MediumScale:MainCheck_MediumScale.cfg;Scenario4_MinimalConstraints:MainCheck_MinimalConstraints.cfg"
SCENARIOS="${SCENARIOS:-$DEFAULT_SCENARIOS}"

if [ "${RUN_MILLION_SCALE}" = "1" ] && [ -f "${PROJECT_DIR}/MainCheck_MillionScale.cfg" ]; then
    SCENARIOS="${SCENARIOS};Scenario5_MillionScale:MainCheck_MillionScale.cfg"
fi

if [ "${RUN_BREAKDOWN_WITNESS}" = "1" ] && [ -f "${PROJECT_DIR}/MainCheckRefinement_BreakdownWitness.cfg" ]; then
    if [ "${MODULE_NAME}" = "MainCheckRefinementWitness" ]; then
        SCENARIOS="${SCENARIOS};Refinement_BreakdownWitness:MainCheckRefinement_BreakdownWitness.cfg"
    else
        echo "Warning: RUN_BREAKDOWN_WITNESS=1 requires MODULE_NAME=MainCheckRefinementWitness. Skipping witness scenario."
    fi
fi

if [ ! -d "${PROJECT_DIR}" ]; then
    echo "Error: MODULE_DIR not found: ${PROJECT_DIR}"
    exit 1
fi

if [ ! -f "${TLA_JAR_PATH}" ]; then
    echo "Error: tla2tools.jar not found at: ${TLA_JAR_PATH}"
    echo "Set TLA_JAR_PATH to the correct jar location."
    exit 1
fi

# Create output directory
mkdir -p "${OUTPUT_DIR}"
mkdir -p "${OUTPUT_DIR}/logs"

# Initialize CSV header
echo "Scenario,Configuration,Timestamp,Status,TotalStates,DistinctStates,Depth,Run1(ms),Run2(ms),Run3(ms),MeanWallTime(ms),StdDev(ms),CI95HalfWidth(ms),ViolationsFound,Notes" > "${RESULTS_CSV}"

# Function to run TLC and extract metrics
run_tlc_scenario() {
    local scenario_name="$1"
    local config_file="$2"
    local scenario_safe
    scenario_safe=$(echo "${scenario_name}" | tr ' /' '__')
    
    echo "=========================================="
    echo "Running Scenario: $scenario_name"
    echo "Config: $config_file"
    echo "Module: $MODULE_NAME"
    echo "=========================================="
    
    local log_file="${OUTPUT_DIR}/logs/${scenario_safe}_${TIMESTAMP}.log"
    
    # Run TLC and capture output with millisecond timing
    cd "${PROJECT_DIR}"
    
    # Get start time in milliseconds using Python
    local start_ms=$(python3 -c "import time; print(int(time.time() * 1000))")
    
    local tlc_output=""
    local exit_code=0
    local run1_ms="N/A"
    local run2_ms="N/A"
    local run3_ms="N/A"
    local timings=()
    local runs_log=""

    for run_idx in $(seq 1 "${RUNS_PER_SCENARIO}"); do
        echo "  -> Trial ${run_idx}/${RUNS_PER_SCENARIO}"

        local run_start_ms=$(python3 -c "import time; print(int(time.time() * 1000))")

        # Run TLC with proper parameters
        tlc_output=$(java -XX:+IgnoreUnrecognizedVMOptions \
            -Dtlc2.TLC.stopAfter="${TLC_STOP_AFTER_SECONDS}" \
            -cp "${TLA_JAR_PATH}" \
            tlc2.TLC \
            -metadir "${PROJECT_DIR}/.tlc_${scenario_safe}_run${run_idx}" \
            -config "${config_file}" \
            -modelcheck \
            "${MODULE_NAME}" \
            2>&1 || true)

        exit_code=$?

        local run_end_ms=$(python3 -c "import time; print(int(time.time() * 1000))")
        local run_time_ms=$((run_end_ms - run_start_ms))
        timings+=("${run_time_ms}")
        runs_log+="\n===== RUN ${run_idx} (${run_time_ms}ms) =====\n${tlc_output}\n"

        if [ "${run_idx}" -eq 1 ]; then
            run1_ms="${run_time_ms}"
        elif [ "${run_idx}" -eq 2 ]; then
            run2_ms="${run_time_ms}"
        else
            run3_ms="${run_time_ms}"
        fi

        if [ ${exit_code} -ne 0 ]; then
            break
        fi
    done

    # Get end time in milliseconds using Python
    local end_ms=$(python3 -c "import time; print(int(time.time() * 1000))")
    local wall_time=$((end_ms - start_ms))

    # Compute robust timing metrics from trial runs (n=3, 95% CI via t distribution with df=2)
    local timing_metrics
    timing_metrics=$(python3 - "${timings[@]}" << 'PY'
import math
import statistics
import sys

vals = [int(v) for v in sys.argv[1:] if v.isdigit()]
if not vals:
    print("N/A,N/A,N/A")
    sys.exit(0)

mean_val = statistics.mean(vals)
if len(vals) > 1:
    std_val = statistics.stdev(vals)
else:
    std_val = 0.0

# 95% two-sided CI half-width uses Student's t critical value.
# Uses a small lookup table (df = n - 1) for stronger statistical validity.
t_critical_by_df = {
    1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571,
    6: 2.447, 7: 2.365, 8: 2.306, 9: 2.262, 10: 2.228,
    11: 2.201, 12: 2.179, 13: 2.160, 14: 2.145, 15: 2.131,
    16: 2.120, 17: 2.110, 18: 2.101, 19: 2.093, 20: 2.086,
    21: 2.080, 22: 2.074, 23: 2.069, 24: 2.064, 25: 2.060,
    26: 2.056, 27: 2.052, 28: 2.048, 29: 2.045, 30: 2.042,
}
df = len(vals) - 1
t_critical = t_critical_by_df.get(df, 1.96)
half_width = t_critical * (std_val / math.sqrt(len(vals))) if len(vals) > 1 else 0.0

print(f"{mean_val:.2f},{std_val:.2f},{half_width:.2f}")
PY
)

    local mean_wall_time=$(echo "${timing_metrics}" | cut -d',' -f1)
    local stddev_ms=$(echo "${timing_metrics}" | cut -d',' -f2)
    local ci95_half_width_ms=$(echo "${timing_metrics}" | cut -d',' -f3)
    
    # Parse results from TLC output using macOS-compatible grep/sed
    local total_states=$(echo "$tlc_output" | grep "states generated" | sed -E 's/^[^0-9]*([0-9]+).*/\1/' | head -1 || echo "N/A")
    local distinct_states=$(echo "$tlc_output" | grep "distinct states found" | sed -E 's/^[^0-9]*([0-9]+).*/\1/' | head -1 || echo "N/A")
    local depth=$(echo "$tlc_output" | grep "depth of the complete state graph search is" | sed -E 's/^.*is[[:space:]]+([0-9]+).*/\1/' | head -1 || echo "N/A")
    
    # Check for violations
    local violations_found="No"
    if echo "$tlc_output" | grep -q "Invariant violated\|property violated\|Error:"; then
        violations_found="Yes"
    fi
    
    # Determine status
    local status="COMPLETE"
    if [ $exit_code -ne 0 ]; then
        status="FAILED"
    elif [ "$violations_found" = "Yes" ]; then
        status="VIOLATIONS_FOUND"
    fi
    
    # Save full log with each trial output
    printf "%b\n" "${runs_log}" > "${log_file}"
    
    # Append to CSV with trial timings and summary statistics
    echo "${scenario_name},${config_file},${TIMESTAMP},${status},${total_states},${distinct_states},${depth},${run1_ms},${run2_ms},${run3_ms},${mean_wall_time},${stddev_ms},${ci95_half_width_ms},${violations_found},Executed successfully" >> "${RESULTS_CSV}"
    
    echo "Status: $status"
    echo "Scenario Wall Time (all 3 runs): ${wall_time}ms"
    echo "Trial Runs: ${run1_ms}ms, ${run2_ms}ms, ${run3_ms}ms"
    echo "Mean ± 95% CI: ${mean_wall_time} ± ${ci95_half_width_ms} ms"
    echo "Total States: $total_states"
    echo "Distinct States: $distinct_states"
    echo "Violations Found: $violations_found"
    echo "Log saved to: $log_file"
    echo ""
}

# Run configured scenarios
IFS=';' read -r -a scenario_entries <<< "${SCENARIOS}"
scenario_count=${#scenario_entries[@]}

for idx in "${!scenario_entries[@]}"; do
    entry="${scenario_entries[$idx]}"
    [ -z "${entry}" ] && continue

    scenario_name="${entry%%:*}"
    config_file="${entry#*:}"

    if [ ! -f "${PROJECT_DIR}/${config_file}" ]; then
        echo "Skipping ${scenario_name}: config not found at ${PROJECT_DIR}/${config_file}"
        continue
    fi

    run_tlc_scenario "${scenario_name}" "${config_file}"

    if [ "$idx" -lt $((scenario_count - 1)) ]; then
        sleep "${SLEEP_BETWEEN_SCENARIOS}"
    fi
done

echo "=========================================="
echo "TEST SUITE COMPLETE"
echo "=========================================="
echo "Results saved to: $RESULTS_CSV"
echo "Logs saved to: ${OUTPUT_DIR}/logs/"
echo ""
echo "Summary:"
column -t -s, < "$RESULTS_CSV"
