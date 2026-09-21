---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANT N \* Number of latches

VARIABLES mode, latchPawlPosition, motorStatus, secondaryReleaseStatus

\* Initial state of the system
Init == /\ mode = [i \in 1..N |-> "RTC"] \* Ready to Capture
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

\* Nominal capture/release sequence
NominalCapture == /\ \E i \in 1..N: mode[i] = "RTC"
                  /\ latchPawlPosition[i] = "unlatched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                  /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

NominalRelease == /\ \E i \in 1..N: mode[i] = "RTR"
                  /\ latchPawlPosition[i] = "latched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                  /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

\* Secondary release operation sequence
SecondaryRelease == /\ \E i \in 1..N: mode[i] = "RTC" /\ motorStatus[i] = "failed"
                     /\ secondaryReleaseStatus[i] = "inactive"
                     /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
                     /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                     /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                     /\ UNCHANGED <<motorStatus>>

Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>
=========================================================================
Define missing recursive function as bracket-domain.
Define missing recursive function as bracket-domain.
====