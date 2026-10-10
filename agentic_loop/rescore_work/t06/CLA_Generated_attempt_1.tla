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

Next == \E i \in 1..NumLatches:
          /\ latchState' = [latchState EXCEPT ![i] = IF motorState[i] = "Failed" THEN "SecondaryRelease" ELSE latchState[i]]
          /\ motorState' = motorState
          /\ secondaryReleaseState' = [secondaryReleaseState EXCEPT ![i] = IF motorState[i] = "Failed" THEN "Active" ELSE secondaryReleaseState[i]]

Spec == Init /\ [][Next]_<<latchState, motorState, secondaryReleaseState>>

=============================================================================