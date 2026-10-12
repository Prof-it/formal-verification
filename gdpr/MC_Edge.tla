---- MODULE MC_Edge ----
EXTENDS MC_GDPR_Time
T(h,mi) == [year|->2025, month|->7, day|->12, hour|->h, minute|->mi]
T2(d,h,mi) == [year|->2025, month|->7, day|->d, hour|->h, minute|->mi]
\* (A) consent and processing logged in the same minute
EvSimultaneous == {
  [type|->"GiveConsent", time|->T(8,20), subject|->"erni", data|->"emaildata"],
  [type|->"StartProcessing", time|->T(8,20), subject|->"erni", data|->"emaildata"]}
\* (B) a malformed/out-of-order entry (withdraw before any consent) followed by an unreported breach
EvBlocked == {
  [type|->"WithdrawConsent", time|->T(8,10), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachDetected", time|->T(8,30), subject|->"erni", data|->"emaildata"],
  [type|->"StartProcessing", time|->T(8,40), subject|->"erni", data|->"emaildata"]}
\* (C) two breaches for same subject/data, one report: late for the first, timely for the second
EvTwoBreaches == {
  [type|->"GiveConsent", time|->T(8,0), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachDetected", time|->T(8,30), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachDetected", time|->T2(14,8,30), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachReported", time|->T2(15,9,0), subject|->"erni", data|->"emaildata"],
  [type|->"StartContract", time|->T2(20,9,0), subject|->"erni", data|->"emaildata"]}
\* (D) consent given, withdrawn, re-given, withdrawn again; processing continues afterwards
EvRegrant == {
  [type|->"GiveConsent", time|->T(8,0), subject|->"erni", data|->"emaildata"],
  [type|->"WithdrawConsent", time|->T(8,10), subject|->"erni", data|->"emaildata"],
  [type|->"GiveConsent", time|->T(8,20), subject|->"erni", data|->"emaildata"],
  [type|->"StartProcessing", time|->T(8,25), subject|->"erni", data|->"emaildata"],
  [type|->"WithdrawConsent", time|->T(8,30), subject|->"erni", data|->"emaildata"]}
\* (E) breach reported after 71 h of real time across the 2024 leap day
TL(y,mo,d,h,mi) == [year|->y, month|->mo, day|->d, hour|->h, minute|->mi]
EvLeap == {
  [type|->"DataBreachDetected", time|->TL(2024,2,28,12,0), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachReported", time|->TL(2024,3,2,11,0), subject|->"erni", data|->"emaildata"]}
\* (F) breach reported after 48 h of real time across the 2020/21 year boundary
EvNewYear == {
  [type|->"DataBreachDetected", time|->TL(2020,12,31,12,0), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachReported", time|->TL(2021,1,2,12,0), subject|->"erni", data|->"emaildata"]}
\* (G) breach on 31 Jan 2024, never reported; a later event on 3 Feb 2024 (real elapsed 84 h)
EvLeapMissing == {
  [type|->"DataBreachDetected", time|->TL(2024,1,31,12,0), subject|->"erni", data|->"emaildata"],
  [type|->"GiveConsent", time|->TL(2024,2,4,0,0), subject|->"bert", data|->"emaildata"]}
\* (H) breach detected 31 Jan 2024 12:00, reported 3 Feb 2024 14:00: 74 h real time, i.e. late
EvLeapLate == {
  [type|->"DataBreachDetected", time|->TL(2024,1,31,12,0), subject|->"erni", data|->"emaildata"],
  [type|->"DataBreachReported", time|->TL(2024,2,3,14,0), subject|->"erni", data|->"emaildata"]}
====
