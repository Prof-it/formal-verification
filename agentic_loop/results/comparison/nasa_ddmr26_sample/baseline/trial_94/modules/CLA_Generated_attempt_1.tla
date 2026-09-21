---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS NumLatches
VARIABLES latchState, latchPosition, motorState, secondaryReleaseState

\* Latch states
LatchStates == {"RTC", "RTR", "SecondaryRelease"}

\* Motor states
MotorStates == {"Operational", "Failed"}

\* Secondary release states
SecondaryReleaseStates == {"Inactive", "Active"}

Init == /\ latchState \in [1..NumLatches -> LatchStates]
        /\ latchPosition \in [1..NumLatches -> {"Latched", "Unlatched"}]
        /\ motorState \in [1..NumLatches -> MotorStates]
        /\ secondaryReleaseState \in [1..NumLatches -> SecondaryReleaseStates]

TypeOK == /\ latchState \in [1..NumLatches -> LatchStates]
          /\ latchPosition \in [1..NumLatches -> {"Latched", "Unlatched"}]
          /\ motorState \in [1..NumLatches -> MotorStates]
          /\ secondaryReleaseState \in [1..NumLatches -> SecondaryReleaseStates]

DDMR26 == \A i \in 1..NumLatches:
            /\ (latchState[i] = "RTC" => latchPosition[i] = "Unlatched")
            /\ (latchState[i] = "RTR" => latchPosition[i] = "Latched")
            /\ (latchState[i] = "SecondaryRelease" => latchPosition[i] = "Unlatched")
            /\ (secondaryReleaseState[i] = "Active" => latchState[i] = "SecondaryRelease")

Next == \E i \in 1..NumLatches:
          \/ /\ latchState[i] = "RTC"
             /\ latchPosition[i] = "Unlatched"
             /\ motorState[i] = "Operational"
             /\ latchState' = [latchState EXCEPT ![i] = "RTR"]
             /\ latchPosition' = [latchPosition EXCEPT ![i] = "Latched"]
             /\ UNCHANGED <<motorState, secondaryReleaseState>>
          \/ /\ latchState[i] = "RTR"
             /\ latchPosition[i] = "Latched"
             /\ motorState[i] = "Operational"
             /\ latchState' = [latchState EXCEPT ![i] = "RTC"]
             /\ latchPosition' = [latchPosition EXCEPT ![i] = "Unlatched"]
             /\ UNCHANGED <<motorState, secondaryReleaseState>>
          \/ /\ motorState[i] = "Failed"
             /\ secondaryReleaseState[i] = "Inactive"
             /\ latchState[i] = "RTC"
             /\ latchPosition[i] = "Latched"
             /\ secondaryReleaseState' = [secondaryReleaseState EXCEPT ![i] = "Active"]
             /\ latchState' = [latchState EXCEPT ![i] = "SecondaryRelease"]
             /\ latchPosition' = [latchPosition EXCEPT ![i] = "Unlatched"]
             /\ UNCHANGED <<motorState>>

Spec == Init /\ [][Next]_<<latchState, latchPosition, motorState, secondaryReleaseState>>

=============================================================================