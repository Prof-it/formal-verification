#!/usr/bin/env bash
# Regression tests for the edge cases discussed in the review. Run from gdpr/ (MC_Edge.tla next to MC_GDPR_Time.tla).
# Each line: scenario  invariant  expected(violated|holds)
set -uo pipefail
J=${1:?path to tla2tools.jar}; [ -f "$J" ] || { echo "tla2tools.jar not found: $J" >&2; exit 2; }
JAR="$(cd "$(dirname "$J")" && pwd)/$(basename "$J")"   # absolute; portable (no realpath)
fail=0
while read -r ev inv exp; do
  cat > /tmp/edge.cfg <<CFG
SPECIFICATION Spec
CONSTANTS
    DataSubjects <- MC_DataSubjects
    Data <- MC_Data
    ObservedEvents <- Ev$ev
    YearRange <- MC_YearRange
    MonthRange <- MC_MonthRange
    DayRange <- MC_DayRange
    HourRange <- MC_HourRange
    MinuteRange <- MC_MinuteRange
    FixedEndTime <- MC_MAX_TIME
INVARIANT $inv
CFG
  out=$(java -cp "$JAR" tlc2.TLC -noGenerateSpecTE -metadir /tmp/edge_states_$ev MC_Edge.tla -config /tmp/edge.cfg 2>&1)
  if grep -q "Invariant $inv is violated" <<<"$out"; then got=violated; else got=holds; fi
  [[ $got == "$exp" ]] && r=OK || { r=FAIL; fail=1; }
  printf "%-5s %-14s %-24s expected=%-9s got=%s\n" "$r" "$ev" "$inv" "$exp" "$got"
done <<'LIST'
Blocked NoRejectedEvents violated
Blocked BreachReportedOnTime violated
Regrant AllProcessingIsLawful violated
LeapLate BreachReportedOnTime violated
Leap BreachReportedOnTime holds
NewYear BreachReportedOnTime holds
Simultaneous AllProcessingIsLawful violated
LIST
exit $fail
