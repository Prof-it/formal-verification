---- MODULE CLA_Generated_attempt_2 ----
EXTENDS Naturals, Sequences

CONSTANT N \* Number of latches

VARIABLES mode, latchPawlPosition, motorStatus, secondaryReleaseStatus

\* Initial state of the system
Init == /\ mode = [i \in 1..N |-> "RTC"]
        /\ latchPawlPosition = [i \in 1..N |-> "unlatched"]
        /\ motorStatus = [i \in 1..N |-> "operational"]
        /\ secondaryReleaseStatus = [i \in 1..N |-> "inactive"]

\* Type invariant
TypeOK == /\ mode \in [1..N -> {"RTC", "RTR", "secondaryRelease"}]
          /\ latchPawlPosition \in [1..N -> {"latched", "unlatched"}]
          /\ motorStatus \in [1..N -> {"operational", "failed"}]
          /\ secondaryReleaseStatus \in [1..N -> {"active", "inactive"}]

\* Problem invariant: Direct indication of critical states
DDMR26 == \A i \in 1..N: 
            /\ (mode[i] = "RTC" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "secondaryRelease" => latchPawlPosition[i] = "unlatched")
            /\ (secondaryReleaseStatus[i] = "active" => mode[i] = "secondaryRelease")

\* Transition for nominal capture/release sequence
NominalCaptureRelease == 
    \E i \in 1..N: 
        /\ mode[i] = "RTC"
        /\ latchPawlPosition[i] = "unlatched"
        /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
        /\ mode' = [mode EXCEPT ![i] = "RTR"]
        /\ motorStatus' = motorStatus
        /\ secondaryReleaseStatus' = secondaryReleaseStatus

\* Transition for secondary release operation sequence
SecondaryRelease == 
    \E i \in 1..N: 
        /\ mode[i] = "RTC"
        /\ motorStatus[i] = "failed"
        /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
        /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
        /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
        /\ motorStatus' = motorStatus

\* Next-state relation
Next == NominalCaptureRelease \/ SecondaryRelease

\* Specification
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>

=========================================================================