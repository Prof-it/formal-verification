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
cd /Users/tianxiang.lu/dev/formal-verification/agentic_loop_paper
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Run With Replay Provider (no API key)

Create replay outputs first (each file should contain one full TLA+ module):

```bash
mkdir -p replay_outputs
# Add 1..N .tla files to replay_outputs/
```

Run baseline mode:

```bash
PYTHONPATH=src python3 -m agentic_loop.cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar /path/to/tla2tools.jar \
  --module-dir /Users/tianxiang.lu/dev/formal-verification/agentic_loop_paper/tla \
  --output-dir results \
  --prompts-dir prompts \
  --mode baseline \
  --prompt-mode one_shot \
  --provider replay \
  --replay-dir replay_outputs
```

Run loop mode:

```bash
PYTHONPATH=src python3 -m agentic_loop.cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar /path/to/tla2tools.jar \
  --module-dir /Users/tianxiang.lu/dev/formal-verification/agentic_loop_paper/tla \
  --output-dir results \
  --prompts-dir prompts \
  --mode loop \
  --max-iterations 3 \
  --prompt-mode one_shot \
  --provider replay \
  --replay-dir replay_outputs
```

## Run With OpenAI-Compatible Provider

```bash
export OPENAI_API_KEY=<api_key>
PYTHONPATH=src python3 -m agentic_loop.cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar /path/to/tla2tools.jar \
  --module-dir /Users/tianxiang.lu/dev/formal-verification/agentic_loop_paper/tla \
  --output-dir results \
  --prompts-dir prompts \
  --mode loop \
  --provider openai \
  --model gpt-5
```

## Run Consolidated Baseline-vs-Loop Comparison

This command runs both modes on the same task and writes a consolidated comparison report.

```bash
PYTHONPATH=src python3 -m agentic_loop.compare_cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar /path/to/tla2tools.jar \
  --module-dir /Users/tianxiang.lu/dev/formal-verification/agentic_loop_paper/tla \
  --output-dir results/comparison \
  --prompts-dir prompts \
  --prompt-mode one_shot \
  --max-iterations 3 \
  --provider replay \
  --replay-dir replay_outputs
```

Generated artifacts:

- `results/comparison/baseline/<task>_run.json`
- `results/comparison/loop/<task>_run.json`
- `results/comparison/comparison_<task>.csv`
- `results/comparison/comparison_<task>.md`

## Output

### CLA Baseline Assets

- `tla/CLA.tla`: reference CLA model used as the paper baseline artifact
- `tla/CLA.cfg`: TLC config for the reference model
- `tla/CLA_generation_eval.cfg`: TLC config used to evaluate generated specifications

The NASA task in `tasks/nasa_ddmr26_sample.yaml` is configured to evaluate generated modules
against `TypeOK` and `DDMR26` using `CLA_generation_eval.cfg`.

Each run writes:

- `<task>_run.json`: full run metadata and attempt details
- `<task>_attempts.csv`: tabular attempt-level summary

These outputs are sufficient to report baseline-vs-loop outcomes with minimal analysis overhead.
