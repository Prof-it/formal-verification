---- MODULE CLA_Generated_attempt_2 ----
EXTENDS Naturals, Sequences

CONSTANTS LATCH_COUNT
VARIABLES latchState, latchPosition, motorStatus, secondaryReleaseStatus

\* Latch states
ReadyToCapture == "RTC"
ReadyToRelease == "RTR"
SecondaryRelease == "SR"

\* Motor status
MotorOperational == "Operational"
MotorFailed == "Failed"

\* Secondary release status
SecondaryReleaseInactive == "Inactive"
SecondaryReleaseActive == "Active"

Init == /\ latchState \in [1..LATCH_COUNT -> {ReadyToCapture, ReadyToRelease, SecondaryRelease}]
        /\ latchPosition \in [1..LATCH_COUNT -> {0, 1}] \* 0 for unlatched, 1 for latched
        /\ motorStatus \in [1..LATCH_COUNT -> {MotorOperational, MotorFailed}]
        /\ secondaryReleaseStatus \in [1..LATCH_COUNT -> {SecondaryReleaseInactive, SecondaryReleaseActive}]

TypeOK == /\ latchState \in [1..LATCH_COUNT -> {ReadyToCapture, ReadyToRelease, SecondaryRelease}]
          /\ latchPosition \in [1..LATCH_COUNT -> {0, 1}]
          /\ motorStatus \in [1..LATCH_COUNT -> {MotorOperational, MotorFailed}]
          /\ secondaryReleaseStatus \in [1..LATCH_COUNT -> {SecondaryReleaseInactive, SecondaryReleaseActive}]

DDMR26 == \A i \in 1..LATCH_COUNT:
            /\ (latchState[i] = ReadyToCapture => latchPosition[i] = 1)
            /\ (latchState[i] = ReadyToRelease => latchPosition[i] = 0)
            /\ (latchState[i] = SecondaryRelease => secondaryReleaseStatus[i] = SecondaryReleaseActive)

Next == \E i \in 1..LATCH_COUNT:
          \/ /\ latchState[i] = ReadyToCapture
             /\ motorStatus[i] = MotorOperational
             /\ latchState' = [latchState EXCEPT ![i] = ReadyToRelease]
             /\ latchPosition' = [latchPosition EXCEPT ![i] = 0]
             /\ UNCHANGED <<motorStatus, secondaryReleaseStatus>>
          \/ /\ latchState[i] = ReadyToRelease
             /\ motorStatus[i] = MotorOperational
             /\ latchState' = [latchState EXCEPT ![i] = ReadyToCapture]
             /\ latchPosition' = [latchPosition EXCEPT ![i] = 1]
             /\ UNCHANGED <<motorStatus, secondaryReleaseStatus>>
          \/ /\ latchState[i] = ReadyToCapture
             /\ motorStatus[i] = MotorFailed
             /\ secondaryReleaseStatus[i] = SecondaryReleaseInactive
             /\ latchState' = [latchState EXCEPT ![i] = SecondaryRelease]
             /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = SecondaryReleaseActive]
             /\ UNCHANGED <<latchPosition, motorStatus>>

Spec == Init /\ [][Next]_<<latchState, latchPosition, motorStatus, secondaryReleaseStatus>>
=========================================================================
Ensure DDMR26 evaluates to a boolean by correcting the logical conditions.
====