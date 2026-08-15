#!/bin/bash
# Regression test for GDPR TLA+ modules and trace visualization
# 1. Detect changes in any .tla file in gdpr/ (for CI: always run, for local: can use git diff)
# 2. For each .cfg file, run TLC model checker using tla2tools.jar
# 3. If all TLC runs succeed, run the Python visualization pipeline

set -e
set -o pipefail

# Directory setup
GDPR_DIR="$(cd "$(dirname "$0")" && pwd)"
TLA_DIR="$GDPR_DIR"
TLA2TOOLS_JAR="$GDPR_DIR/../tla_modules/tla2tools.jar"
TRACE2VIS_PIPELINE="$GDPR_DIR/trace2vis/tla_time_viz_pipeline.py"
VENV_ACTIVATE="$GDPR_DIR/trace2vis/venv/bin/activate"

# 1. Find all TLA+ modules and config files
TLA_MODULES=("$GDPR_DIR"/*.tla)
CFG_FILES=("$GDPR_DIR"/*.cfg)

echo "[INFO] Checking TLA+ modules: ${TLA_MODULES[*]}"
echo "[INFO] Checking config files: ${CFG_FILES[*]}"

# 2. Run TLC model checker for each config
ALL_OK=1
for cfg in "${CFG_FILES[@]}"; do
  # Derive the corresponding TLA module (assume MC_*.cfg -> MC_GDPR_Time.tla)
  # Use MC_GDPR_Time.tla for all configs as per project structure
  tla="$GDPR_DIR/MC_GDPR_Time.tla"
  if [[ ! -f "$tla" ]]; then
    echo "[ERROR] TLA+ module $tla not found for config $cfg"
    ALL_OK=0
    continue
  fi
  # Output file: base name without .cfg or any extension
  base="${cfg%.*}"
  out_file="$base.out"
  echo "[INFO] Running TLC for $cfg ..."
  java -cp "$TLA2TOOLS_JAR" tlc2.TLC "$tla" -config "$cfg" > "$out_file" 2>&1 || ALL_OK=0
  # Check for errors in output
  if grep -q "Error:" "$out_file"; then
    echo "[ERROR] TLC found errors in $cfg (see $out_file)"
    ALL_OK=0
  else
    echo "[INFO] TLC completed for $cfg (see $out_file)"
  fi
done

# 3. If all TLC runs succeeded, run the Python visualization pipeline
if [[ $ALL_OK -eq 1 ]]; then
  echo "[INFO] All TLC checks passed. No need to run visualization pipeline."
else
  echo "[INFO] Some violations found. Running visualization pipeline..."
  if [[ -f "$VENV_ACTIVATE" ]]; then
    OLD_PWD="$PWD"
    cd "$GDPR_DIR/trace2vis"
    source venv/bin/activate
    python tla_time_viz_pipeline.py
    cd "$OLD_PWD"
  else
    echo "[ERROR] Python venv not found at $VENV_ACTIVATE. Please set up the venv in trace2vis/."
  fi
fi

echo "[INFO] Regression test complete."

