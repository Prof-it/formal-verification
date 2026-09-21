---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS NumLatches

VARIABLES latchState, motorState, secondaryReleaseState

\* Latch states
LatchStates == {"RTC", "RTR", "SecondaryRelease"}

\* Motor states
MotorStates == {"Operational", "Failed"}

\* Secondary release states
SecondaryReleaseStates == {"Inactive", "Active"}

Init == /\ latchState \in [1..NumLatches -> LatchStates]
        /\ motorState \in [1..NumLatches -> MotorStates]
        /\ secondaryReleaseState \in [1..NumLatches -> SecondaryReleaseStates]
        /\ \A i \in 1..NumLatches: latchState[i] = "RTC"
        /\ \A i \in 1..NumLatches: motorState[i] = "Operational"
        /\ \A i \in 1..NumLatches: secondaryReleaseState[i] = "Inactive"

TypeOK == /\ latchState \in [1..NumLatches -> LatchStates]
          /\ motorState \in [1..NumLatches -> MotorStates]
          /\ secondaryReleaseState \in [1..NumLatches -> SecondaryReleaseStates]

DDMR26 == \A i \in 1..NumLatches:
            \/ latchState[i] = "RTC"
            \/ latchState[i] = "RTR"
            \/ latchState[i] = "SecondaryRelease"

NominalCaptureRelease == 
    /\ \E i \in 1..NumLatches: latchState[i] = "RTC"
    /\ \E i \in 1..NumLatches: latchState[i]' = "RTR"
    /\ motorState' = motorState
    /\ secondaryReleaseState' = secondaryReleaseState

SecondaryReleaseOperation == 
    /\ \E i \in 1..NumLatches: latchState[i] = "RTC" /\ motorState[i] = "Failed"
    /\ latchState' = [latchState EXCEPT ![i] = "SecondaryRelease"]
    /\ secondaryReleaseState' = [secondaryReleaseState EXCEPT ![i] = "Active"]
    /\ motorState' = motorState

Next == NominalCaptureRelease \/ SecondaryReleaseOperation

Spec == Init /\ [][Next]_<<latchState, motorState, secondaryReleaseState>>

=========================================================================
Define missing recursive function as bracket-domain.
Define missing recursive function as bracket-domain.
====