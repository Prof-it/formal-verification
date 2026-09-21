---- MODULE CLA_Generated_attempt_2 ----
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

\* Problem invariant capturing the critical state indication requirement
DDMR26 == \A i \in 1..N: 
            /\ (mode[i] = "RTC" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "RTR" => latchPawlPosition[i] = "unlatched")
            /\ (mode[i] = "secondaryRelease" => latchPawlPosition[i] = "unlatched")
            /\ (secondaryReleaseStatus[i] = "active" => mode[i] = "secondaryRelease")

\* Steps representing the transitions of the system
ReadyToCapture == \E i \in 1..N: /\ mode[i] = "RTR"
                                /\ mode' = [mode EXCEPT ![i] = "RTC"]
                                /\ latchPawlPosition' = latchPawlPosition
                                /\ motorStatus' = motorStatus
                                /\ secondaryReleaseStatus' = secondaryReleaseStatus

Capture == \E i \in 1..N: /\ mode[i] = "RTC" /\ latchPawlPosition[i] = "unlatched"
                         /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                         /\ mode' = mode
                         /\ motorStatus' = motorStatus
                         /\ secondaryReleaseStatus' = secondaryReleaseStatus

Release == \E i \in 1..N: /\ mode[i] = "RTR" /\ latchPawlPosition[i] = "latched"
                         /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                         /\ mode' = mode
                         /\ motorStatus' = motorStatus
                         /\ secondaryReleaseStatus' = secondaryReleaseStatus

SecondaryRelease == \E i \in 1..N: /\ mode[i] = "RTC" /\ motorStatus[i] = "failed"
                                   /\ secondaryReleaseStatus' = [secondaryReleaseStatus EXCEPT ![i] = "active"]
                                   /\ mode' = [mode EXCEPT ![i] = "secondaryRelease"]
                                   /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                                   /\ motorStatus' = motorStatus

Next == \/ ReadyToCapture
        \/ Capture
        \/ Release
        \/ SecondaryRelease

Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>
=========================================================================