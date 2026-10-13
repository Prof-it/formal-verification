#!/usr/bin/env bash
# Regenerate all paper figures from TLC counterexamples.
# Usage: trace2tikz/make_figures.sh /path/to/tla2tools.jar [out_dir]   (out_dir default: trace2tikz/report)
# Keeps per scenario: <cfg>.json (TLC trace), <cfg>.tex, <cfg>.summary.json, <cfg>.pdf
set -euo pipefail
J=${1:?path to tla2tools.jar}; [ -f "$J" ] || { echo "tla2tools.jar not found: $J" >&2; exit 2; }
JAR="$(cd "$(dirname "$J")" && pwd)/$(basename "$J")"   # absolute; portable (no realpath)
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${2:-$HERE/report}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)   # absolute, because we cd below
cd "$HERE/.."                                                       # gdpr/, where the model lives
while read -r cfg inv title; do
  java -cp "$JAR" tlc2.TLC -noGenerateSpecTE -metadir "$OUT/states_$cfg" -dumpTrace json "$OUT/$cfg.json" \
       MC_GDPR_Time.tla -config "$cfg.cfg" > "$OUT/$cfg.out" 2>&1 || true   # TLC exits non-zero on violation
  grep -q "is violated" "$OUT/$cfg.out" || { echo "[$cfg] no violation, skipped"; rm -rf "$OUT/states_$cfg"; continue; }
  python3 "$HERE/trace2tikz.py" "$OUT/$cfg.json" --invariant "$inv" \
          --width-cm 5.4 -o "$OUT/$cfg.tex" --summary "$OUT/$cfg.summary.json"
  (cd "$OUT" && pdflatex -interaction=nonstopmode -halt-on-error "$cfg.tex" > /dev/null)
  rm -rf "$OUT/states_$cfg" "$OUT/$cfg.out" "$OUT/$cfg.aux" "$OUT/$cfg.log"
  echo "[$cfg] -> $OUT/$cfg.pdf"
done <<'LIST'
MC_ConsentWithdrawn AllProcessingIsLawful Consent_withdrawn
MC_MissingConsent AllProcessingIsLawful Missing_consent
MC_DeadlineViolation BreachReportedOnTime Breach_report_missing
MC_ReportBreachLate BreachReportedOnTime Breach_reported_late
LIST
