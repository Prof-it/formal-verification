#!/usr/bin/env bash
# Regenerate all paper figures from TLC counterexamples. Run from the gdpr/ directory.
# Usage: ./make_figures.sh /path/to/tla2tools.jar out_dir
set -euo pipefail
J=${1:?path to tla2tools.jar}; [ -f "$J" ] || { echo "tla2tools.jar not found: $J" >&2; exit 2; }
JAR="$(cd "$(dirname "$J")" && pwd)/$(basename "$J")"   # absolute; portable (no realpath)
OUT=${2:-report}; HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
while read -r cfg inv title; do
  java -cp "$JAR" tlc2.TLC -metadir "$OUT/states_$cfg" -dumpTrace json "$OUT/$cfg.json" \
       MC_GDPR_Time.tla -config "$cfg.cfg" > "$OUT/$cfg.out" 2>&1 || true   # TLC exits non-zero on violation
  grep -q "is violated" "$OUT/$cfg.out" || { echo "[$cfg] no violation, skipped"; continue; }
  python3 "$HERE/trace2tikz.py" "$OUT/$cfg.json" --invariant "$inv" \
          --width-cm 5.4 -o "$OUT/$cfg.tex" --summary "$OUT/$cfg.summary.json"
  (cd "$OUT" && pdflatex -interaction=nonstopmode -halt-on-error "$cfg.tex" > /dev/null)
  echo "[$cfg] -> $OUT/$cfg.pdf"
done <<'LIST'
MC_ConsentWithdrawn AllProcessingIsLawful Consent_withdrawn
MC_MissingConsent AllProcessingIsLawful Missing_consent
MC_DeadlineViolation BreachReportedOnTime Breach_report_missing
MC_ReportBreachLate BreachReportedOnTime Breach_reported_late
LIST
