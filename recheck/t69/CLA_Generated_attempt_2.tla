---- MODULE CLA_Generated_attempt_2 ----
EXTENDS Naturals, Sequences

CONSTANTS LATCH_COUNT
VARIABLES latchState, latchPosition, motorStatus, secondaryReleaseStatus

\* Initial state of the system
Init == /\ latchState \in [1..LATCH_COUNT -> {"RTC", "RTR", "SecondaryRelease"}]
        /\ latchPosition \in [1..LATCH_COUNT -> {"Latched", "Unlatched"}]
        /\ motorStatus \in [1..LATCH_COUNT -> {"Operational", "Failed"}]
        /\ secondaryReleaseStatus \in [1..LATCH_COUNT -> BOOLEAN]
        /\ \A i \in 1..LATCH_COUNT: latchState[i] = "RTC" /\ latchPosition[i] = "Unlatched" /\ motorStatus[i] = "Operational" /\ secondaryReleaseStatus[i] = FALSE

\* Type invariant ensuring all variables are within their expected domains
TypeOK == /\ latchState \in [1..LATCH_COUNT -> {"RTC", "RTR", "SecondaryRelease"}]
          /\ latchPosition \in [1..LATCH_COUNT -> {"Latched", "Unlatched"}]
          /\ motorStatus \in [1..LATCH_COUNT -> {"Operational", "Failed"}]
          /\ secondaryReleaseStatus \in [1..LATCH_COUNT -> BOOLEAN]

\* Problem invariant representing the requirement for direct indication of critical states
DDMR26 == \A i \in 1..LATCH_COUNT:
            /\ (latchState[i] = "RTC" => latchPosition[i] = "Unlatched")
            /\ (latchState[i] = "RTR" => latchPosition[i] = "Latched")
            /\ (latchState[i] = "SecondaryRelease" => secondaryReleaseStatus[i] = TRUE)

\* Transition for nominal capture/release sequence
NominalSequence == 
    \E i \in 1..LATCH_COUNT:
        /\ latchState[i] = "RTC"
        /\ latchPosition[i] = "Unlatched"
        /\ latchState' = [latchState EXCEPT ![i] = "RTR"]
        /\ latchPosition' = [latchPosition EXCEPT ![i] = "Latched"]
        /\ UNCHANGED <<motorStatus, secondaryReleaseStatus>>

\* Transition for secondary release operation sequence
SecondaryReleaseSequence ==
    \E i \in 1..LATCH_COUNT:
        /\ latchState[i] = "RTC"
        /\ latchPosition[i] = "Latched"
        /\ motorStatus[i] = "Failed"
        /\ secondaryReleaseStatus[i] = FALSE
        /\ latchState' = [latchState EXCEPT ![i] = "SecondaryRelease"]
        /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = TRUE]
        /\ UNCHANGED <<latchPosition, motorStatus>>

\* Next-state relation
Next == NominalSequence \/ SecondaryReleaseSequence

\* Specification of the system
Spec == Init /\ [][Next]_<<latchState, latchPosition, motorStatus, secondaryReleaseStatus>>

=========================================================================