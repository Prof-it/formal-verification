# Agentic Loop Paper Subproject

---


## Key Principles and Outcome (2026)

- **Regression-proof modular human-in-the-loop repair:**
  - All repairs are strictly TLC-gated: no unverified repair can ever overwrite or regress a verified artifact. Baseline and loop modes use paired initial LLM generation for proper experimental control.
  - Unknown error types are presented to the LLM for modular repair/rule suggestion, but *no rule is added/applied unless it is explicitly human-approved*.
  - All persistent memory is a human-approved modular rule database; there is **no agentic learning or policy adaptation**.

- **Empirical results (NASA DDMR-26, N=100):**
  - Baseline TLC pass rate: 20.0% (20/100)
  - Loop/repair TLC pass rate: 88.0% (88/100)
  - 68 of 80 (85%) initially failing specs were rescued; 0 regressions (every pass preserved)
  - All results, rule approvals, and metrics are provided in CSV/Markdown outputs in `results/`


This subproject is isolated from the main repository workflow and provides a compact, fully auditable platform for NL-to-TLA experiment runs used in the paper.

## Scope

- Reproduces baseline and loop/repair modes from a paired initial LLM generation.
- Implements modular, *regression-proof* verifier-in-the-loop repair, driven by TLC gate and explicit human rule approval.
- No agentic "skills" or implicit learning: only human-reviewed rules are ever persisted.
- Experiment modes:
  - `baseline`: one-shot LLM generation, verification only
  - `loop`: TLC-gated modular repair up to `max_iterations` (repair stops at first TLC pass or max attempts)

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



## How It Works: Recommended Workflow

The main paired-verification experiment uses `compare_cli`, running multiple stochastic trials for both modes, always starting from paired initial generations. All repairs are regression-proof: any previously TLC-passing artifact is retained and cannot be overwritten, even if repairs are iterated. Results demonstrate large improvements in TLC success with no regressions.

### Using Live LLMs vs. Replay Mode

**By default, we recommend running with your LLM provider (e.g. OpenAI, GPT-4o) for "live" generations:**

**Example: NASA DDMR-26, 10 Trials, OpenAI Provider**
```bash
cd agentic_loop
source .venv/bin/activate
PYTHONPATH=src python -m agentic_loop.compare_cli \
  --task tasks/nasa_ddmr26_sample.yaml \
  --tla-jar tla/tla2tools.jar \
  --module-dir tla \
  --prompts-dir prompts \
  --prompt-mode one_shot \
  --max-iterations 2 \
  --provider openai \
  --model gpt-4o \
  --output-dir results/comparison \
  --num-trials 10
```

- This calls the LLM API for each new trial, generating fresh output per run.
- Use this for new projects, ongoing prompt improvements, or to explore genuine LLM variability.

**For exact reproducibility and debugging:**
Use replay mode to consume *pre-cached* LLM outputs and avoid API calls:
```bash
PYTHONPATH=src python -m agentic_loop.compare_cli \
  ... \
  --provider replay \
  --replay-dir replay_outputs
```
- Only use this if you have generated and stored all needed outputs in the `replay_outputs/` directory, with the correct configuration (task, prompt, model, etc.).


#### Key parameters:
- `--num-trials N` — Number of independent paired trials per mode (use 10+ for confidence)
- `--module-dir tla` — Directory with static TLA models and configs
- `--max-iterations K` — Maximum repair attempts per trial
- `--prompt-mode` — Use `one_shot` for reliable reproducibility

#### Output structure:


Results are saved in subdirectories for each trial and mode under `results/comparison/<task_name>/`, e.g.:

```
results/comparison/nasa_ddmr26_sample/
   baseline/
     trial_01/metrics.csv
     ...
     trial_100/metrics.csv
   loop/
     trial_01/metrics.csv
     ...
     trial_100/metrics.csv
   comparison_nasa_ddmr26_sample.csv      # Aggregated per-trial summary
   comparison_nasa_ddmr26_sample.md       # Markdown summary of all trials/results
```

Each `metrics.csv`/`.json` gives all per-trial outcome details. Aggregate CSV/Markdown files include success rates, rescue counts, zero-regression statistics, CRSR, and class analysis.


#### **When to use which mode**
- `--provider openai` (default):  For new empirical runs and recording new results
- `--provider replay`:  For reproducibility, audit, or CI, after outputs are recorded

You may re-run with a different provider (e.g. `--provider openai --model gpt-4o`) or non-default seeds as needed.


## Reproducing the NASA DDMR26 Experiment

To run the agentic loop comparison for the NASA DDMR26 sample task and save results under `results/nasa_ddmr26`:

1. **Change into the agentic_loop directory:**
   ```sh
   cd /Users/tianxiang.lu/dev/formal-verification/agentic_loop
   ```

2. **Activate the Python virtual environment:**
   ```sh
   source .venv/bin/activate
   ```

3. **Run the experiment CLI:**
   ```sh
   PYTHONPATH=src python -m agentic_loop.compare_cli \
     --task tasks/nasa_ddmr26_sample.yaml \
     --tla-jar tla/tla2tools.jar \
     --output-dir results/nasa_ddmr26 \
     --prompts-dir prompts \
     --prompt-mode one_shot \
     --max-iterations 3 \
     --provider openai \
     --model gpt-4o \
     --module-dir tla
   ```

**Result files** will appear in:
```
agentic_loop/results/nasa_ddmr26/nasa_ddmr26/comparison_nasa_ddmr26.csv
agentic_loop/results/nasa_ddmr26/nasa_ddmr26/comparison_nasa_ddmr26.md
```
and metrics for each trial/mode are in subfolders within `results/nasa_ddmr26/nasa_ddmr26/`.

**Requirements:**
- `tla2tools.jar`, `CLA_Generated.tla`, `CLA_generation_eval.cfg`, and `manifest.json` must all be present in the `tla/` directory.
- All commands should be run from within the `agentic_loop` directory.

---


---


## Output and Artifacts

All outputs include breakdowns of pass/fail/regress, rescue counts, failure class repairability, and all rule approval history, providing a full audit trail for reproducibility/validation.

### Main NASA DDMR-26 Results

- Baseline TLC pass rate: 20/100 (20.0%)
- Loop TLC pass rate after regression-proof repair: 88/100 (88.0%)
- CRSR (previously failing rescued): 68/80 (85%)
- Regressions: 0/20 (every TLC-passing candidate preserved)

---


### Failure Class Repairability (Sample: NASA DDMR-26)

| Failure class                | Baseline Fails | Loop Fails | Repaired | Repair Rate |
|-----------------------------|----------------|------------|----------|-------------|
| missing_next_state_assignment| 27             | 0          | 27       | 100%        |
| unknown                     | 50             | 9          | 41       | 82%         |
| semantic_error_boolean_eval  | 3              | 3          | 0        | 0%          |

All others and run metadata appear per-trial and in aggregates.


## Implementation Details

- Human-in-the-loop repair, gated by TLC.
- Modular rule approvals (no new rule applied without explicit user acceptance).
- Rulebase is persistent and growing: all memory is via explicit rule acceptance, not implicit "learning" or experience.
- All result metrics, rule approvals, skills, and failures are directly linked for each run.


## 📚 Publication

This repository accompanies the following research contribution:


- **Lu, T. (2026).** *Verifier-Guided Repair of LLM-Generated Formal Specifications: A Paired Study on NASA DDMR-26.* IEEE 2026 International Conference on Emerging Trends in Engineering and Computing (ETECOM), Paris, France, 26–27 October 2026. Camera-ready.

```bibtex
@inproceedings{lu2026verifier,
  author    = {Lu, Tianxiang},
  title     = {Verifier-Guided Repair of LLM-Generated Formal Specifications: A Paired Study on NASA DDMR-26},
  booktitle = {IEEE 2026 International Conference on Emerging Trends in Engineering and Computing (ETECOM)},
  year      = {2026},
  address   = {Paris, France},
  month     = oct,
  note      = {Camera-ready; conference scheduled for 26--27 October 2026}
}
```
