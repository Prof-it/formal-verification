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

\* Problem invariant representing DDMR 26 requirement
DDMR26 == \A i \in 1..N: 
            /\ (mode[i] = "RTC" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "latched")
            /\ (mode[i] = "secondaryRelease" => secondaryReleaseStatus[i] = "active")

\* Steps representing the transitions of the system
ReadyToCapture == \E i \in 1..N: 
                    /\ mode[i] = "RTC"
                    /\ latchPawlPosition[i] = "unlatched"
                    /\ mode' = [mode EXCEPT ![i] = "RTR"]
                    /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                    /\ UNCHANGED <<motorStatus, secondaryReleaseStatus>>

ReadyToRelease == \E i \in 1..N: 
                    /\ mode[i] = "RTR"
                    /\ latchPawlPosition[i] = "latched"
                    /\ mode' = [mode EXCEPT ![i] = "RTC"]
                    /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                    /\ UNCHANGED <<motorStatus, secondaryReleaseStatus>>

SecondaryRelease == \E i \in 1..N: 
                      /\ mode[i] = "secondaryRelease"
                      /\ secondaryReleaseStatus[i] = "inactive"
                      /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                      /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
                      /\ UNCHANGED <<latchPawlPosition, motorStatus>>

Next == ReadyToCapture \/ ReadyToRelease \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>

=============================================================================