# Agentic Loop Paper Subproject

This subproject is isolated from the main repository workflow and provides a compact platform for NL-to-TLA experiment runs used in the paper.

## Scope

- Reuses baseline prompt strategy (zero-shot and one-shot) for reproducible NL-to-TLA experiments.
- Adds a verifier-in-the-loop repair cycle driven by TLC feedback.
- Supports two experiment modes:
  - `baseline`: one generation attempt
  - `loop`: iterative repair up to `max_iterations`

## Layout

- `prompts/`: baseline and repair prompt templates
- `tasks/`: YAML task definitions
- `src/agentic_loop/`: platform implementation
- `results/`: run outputs (JSON and CSV)

## Install

```bash
cd /Users/tianxiang.lu/dev/formal-verification/agentic_loop
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Run Multi-Trial Baseline-vs-Loop Stochastic Comparison (Recommended)

The recommended scientific workflow uses the `compare_cli` tool with multiple stochastic trials per mode.
This supports robust statistics and reproducible empirical analysis. Use the correct module and replay directories as below.

**Example: NASA DDMR-26, 10 Trials, Replay Provider**

```bash
source .venv/bin/activate
cd agentic_loop
PYTHONPATH=src python -m agentic_loop.compare_cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar tla/tla2tools.jar \
  --module-dir tla \
  --prompts-dir prompts \
  --prompt-mode one_shot \
  --max-iterations 2 \
  --provider replay \
  --replay-dir replay_outputs \
  --model gpt-4o \
  --output-dir results/comparison \
  --num-trials 10
```

#### Key parameters:
- `--num-trials N` — Number of independent stochastic evaluations per mode (use 10+ for scientific confidence).
- `--module-dir tla` — Directory with static TLA models and configs.
- `--replay-dir replay_outputs` — Where replay TLA generation artifacts are stored.

#### Output structure:

Results will be saved in subdirectories for each trial and mode under `results/comparison/<task_name>/`, e.g.:
```
results/comparison/nasa_ddmr26/
   baseline/
     trial_01/metrics.csv
     ...
     trial_10/metrics.csv
   loop/
     trial_01/metrics.csv
     ...
     trial_10/metrics.csv
   comparison_nasa_ddmr26.csv      # Aggregated per-trial summary, all modes
   comparison_nasa_ddmr26.md       # Markdown summary of all trials
```
Each `metrics.csv` file contains all essential per-trial outcome details (parse/semantic/TLC/repair).
The aggregate CSV and Markdown files summarize all trials for both modes.

You may re-run with a different provider (e.g. `--provider openai --model gpt-4o`) or non-default seeds as needed.

## Output and Artifacts

### NASA DDMR-26 Baseline Assets

- `tla/CLA.tla`: Reference CLA model
- `tla/CLA.cfg`: TLC config for the reference model
- `tla/CLA_generation_eval.cfg`: TLC config for generated or repaired modules

The NASA task YAML (`tasks/nasa_ddmr26_sample.yaml`) is evaluated against invariants (`TypeOK`, `DDMR26`) via `CLA_generation_eval.cfg`.

**For each experiment run**:
- Aggregated metrics are written to `results/comparison/<task_name>/comparison_<task_name>.csv` and `.md`.
- Each mode and each trial gets a subdirectory, e.g. `baseline/trial_01/metrics.csv`.
- All per-attempt and per-trial details are included for scientific, publication-ready reporting.

## Metric Instrumentation

Automated runs persist the evaluation metrics enumerated in [`verifier_in_the_loop.tex`](agentic_loop/verifier_in_the_loop.tex:105). [`persist_run_result`](agentic_loop/src/agentic_loop/reporting.py:15) emits JSON fields for generation and verification success, counterexample statistics, skill usage traces, learning step indices, and human intervention flags. [`compare_cli`](agentic_loop/src/agentic_loop/compare_cli.py:37) consumes these values when producing CSV/Markdown summaries and can optionally aggregate learning efficiency across runs via `--learning-series` inputs.
