---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS N \* Number of latches

VARIABLES mode, latchPawlPosition, motorStatus, secondaryReleaseStatus

\* Initial state of the system
Init == /\ mode = [i \in 1..N |-> "RTC"]
        /\ latchPawlPosition = [i \in 1..N |-> "unlatched"]
        /\ motorStatus = [i \in 1..N |-> "operational"]
        /\ secondaryReleaseStatus = [i \in 1..N |-> "inactive"]

\* Type invariant for the system
TypeOK == /\ mode \in [1..N -> {"RTC", "RTR", "secondaryRelease"}]
          /\ latchPawlPosition \in [1..N -> {"latched", "unlatched"}]
          /\ motorStatus \in [1..N -> {"operational", "failed"}]
          /\ secondaryReleaseStatus \in [1..N -> {"active", "inactive"}]

\* Problem invariant representing DDMR26 requirement
DDMR26 == \A i \in 1..N: 
            /\ (mode[i] = "RTC" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "secondaryRelease" => latchPawlPosition[i] = "unlatched")
            /\ (secondaryReleaseStatus[i] = "active" => mode[i] = "secondaryRelease")

\* Steps representing the transitions of the system
ReadyToCapture == /\ \E i \in 1..N: mode[i] = "RTC"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]

ReadyToRelease == /\ \E i \in 1..N: mode[i] = "RTR"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]

SecondaryRelease == /\ \E i \in 1..N: secondaryReleaseStatus[i] = "active"
                    /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                    /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]

Next == \/ ReadyToCapture
        \/ ReadyToRelease
        \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>

=========================================================================
Define missing recursive function as bracket-domain.
====