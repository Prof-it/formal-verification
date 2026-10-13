#!/bin/bash
# Regression test for the GDPR TLA+ model and the trace visualization.
#   1. every scenario configuration against its expected verdict
#   2. edge cases (run_edge_cases.sh)
#   3. ToMinutes against Python datetime (tools/check_timeutils.py)
#   4. figures from the counterexamples (trace2tikz/make_figures.sh), unless --no-figures
# Usage: ./regression_test.sh [path/to/tla2tools.jar] [--no-figures]
# Exit code 0 only if every verdict matches. TLC output goes to gdpr/out/, figures to trace2tikz/report/.

set -uo pipefail

GDPR_DIR="$(cd "$(dirname "$0")" && pwd)"
J="${1:-$GDPR_DIR/../tla_modules/tla2tools.jar}"
[[ "$J" == --* ]] && J="$GDPR_DIR/../tla_modules/tla2tools.jar"
[ -f "$J" ] || { echo "[ERROR] tla2tools.jar not found: $J" >&2; exit 2; }
TLA2TOOLS_JAR="$(cd "$(dirname "$J")" && pwd)/$(basename "$J")"
FIGURES=1; for arg in "$@"; do [[ "$arg" == --no-figures ]] && FIGURES=0; done
OUT_DIR="$GDPR_DIR/out"
mkdir -p "$OUT_DIR"
cd "$GDPR_DIR"
java -cp "$TLA2TOOLS_JAR" tlc2.TLC 2>&1 | grep -m1 "TLC2 Version" | sed 's/^/[INFO] /'

FAIL=0

# 1. Scenarios: config, expected result ("holds" or the invariant expected to be violated).
#    MC_Scale.cfg is not listed: it belongs to the generated MC_Scale.tla (gen_scale.py).
echo "[INFO] 1. Scenarios"
while read -r cfg expected; do
  out_file="$OUT_DIR/$cfg.out"
  java -cp "$TLA2TOOLS_JAR" tlc2.TLC -noGenerateSpecTE -metadir "$OUT_DIR/states_$cfg" \
       -dumpTrace json "$OUT_DIR/$cfg.json" MC_GDPR_Time.tla -config "$cfg.cfg" > "$out_file" 2>&1
  if grep -q "No error has been found" "$out_file"; then
    got=holds
  elif inv=$(grep -oE "Invariant [A-Za-z]+ is violated" "$out_file"); then
    got=$(awk '{print $2}' <<<"$inv")
  else
    got="TLC-error"
  fi
  states=$(grep -oE "[0-9,]+ distinct states found, [0-9,]+ states left" "$out_file" | tail -1 | cut -d' ' -f1)
  if [[ "$got" == "$expected" ]]; then r=OK; else r=FAIL; FAIL=1; fi
  printf "  %-5s %-28s expected=%-22s got=%-22s states=%s\n" "$r" "$cfg" "$expected" "$got" "${states:--}"
  [[ "$got" == "TLC-error" ]] && tail -5 "$out_file" | sed 's/^/        /'
done <<'LIST'
MC_GDPR_Time holds
MC_ValidConsent holds
MC_ReportBreachNoViolation holds
MC_MissingConsent AllProcessingIsLawful
MC_ConsentWithdrawn AllProcessingIsLawful
MC_DeadlineViolation BreachReportedOnTime
MC_ReportBreachLate BreachReportedOnTime
LIST

# 2. Edge cases
echo "[INFO] 2. Edge cases"
./run_edge_cases.sh "$TLA2TOOLS_JAR" | sed 's/^/  /' || FAIL=1

# 3. Calendar arithmetic
echo "[INFO] 3. ToMinutes vs Python datetime"
python3 tools/check_timeutils.py . "$TLA2TOOLS_JAR" | sed 's/^/  /' || FAIL=1

# 4. Figures
if [[ $FIGURES -eq 1 ]]; then
  echo "[INFO] 4. Figures"
  bash trace2tikz/make_figures.sh "$TLA2TOOLS_JAR" "$GDPR_DIR/trace2tikz/report" | sed 's/^/  /' || FAIL=1
fi

if [[ $FAIL -eq 0 ]]; then echo "[INFO] Regression test passed."; else echo "[ERROR] Regression test FAILED."; fi
exit $FAIL
