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
          /\ secondaryReleaseStatus \in [1..N -> {"inactive", "active"}]

\* Problem invariant: Direct indication of critical states
DDMR26 == \A i \in 1..N: 
            /\ (mode[i] = "RTC" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "secondaryRelease" => latchPawlPosition[i] = "unlatched")
            /\ (secondaryReleaseStatus[i] = "active" => mode[i] = "secondaryRelease")

\* State transitions
NominalCapture == \E i \in 1..N: 
                    /\ mode[i] = "RTC"
                    /\ latchPawlPosition[i] = "unlatched"
                    /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                    /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

NominalRelease == \E i \in 1..N: 
                    /\ mode[i] = "RTR"
                    /\ latchPawlPosition[i] = "latched"
                    /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                    /\ UNCHANGED <<mode, motorStatus, secondaryReleaseStatus>>

SecondaryRelease == \E i \in 1..N: 
                      /\ mode[i] = "RTC"
                      /\ motorStatus[i] = "failed"
                      /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
                      /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                      /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                      /\ UNCHANGED <<motorStatus>>

Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>
=========================================================================