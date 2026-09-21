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
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "latched")
            /\ (mode[i] = "secondaryRelease" => secondaryReleaseStatus[i] = "active")

\* Steps for nominal capture/release sequence
NominalCapture == /\ \E i \in 1..N: mode[i] = "RTC"
                  /\ latchPawlPosition[i] = "unlatched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                  /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

NominalRelease == /\ \E i \in 1..N: mode[i] = "RTR"
                  /\ latchPawlPosition[i] = "latched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                  /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

\* Steps for secondary release operation sequence
SecondaryRelease == /\ \E i \in 1..N: mode[i] = "RTC" /\ motorStatus[i] = "failed"
                     /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
                     /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                     /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                     /\ UNCHANGED <<motorStatus>>

Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>
=========================================================================
Define missing recursive function as bracket-domain.
Define missing recursive function as bracket-domain.
====