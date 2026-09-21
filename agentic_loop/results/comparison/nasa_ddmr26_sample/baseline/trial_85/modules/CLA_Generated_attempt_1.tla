---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS N \* Number of latches

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
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "latched")
            /\ (mode[i] = "secondaryRelease" => secondaryReleaseStatus[i] = "active")

\* Steps in the nominal capture/release sequence
NominalCapture == /\ mode' = [mode EXCEPT ![1] = "RTC"]
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![1] = "latched"]

NominalRelease == /\ mode' = [mode EXCEPT ![1] = "RTR"]
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![1] = "unlatched"]

\* Steps in the secondary release operation sequence
SecondaryRelease == /\ mode' = [mode EXCEPT ![1] = "secondaryRelease"]
                     /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![1] = "active"]

\* Next-state relation
Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

\* Specification
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>

=========================================================================
Assign all next-state vars.
====