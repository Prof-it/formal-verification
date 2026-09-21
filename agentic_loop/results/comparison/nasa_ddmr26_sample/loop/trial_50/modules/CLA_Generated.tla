---- MODULE CLA_Generated_attempt_2 ----
EXTENDS Naturals, Sequences

CONSTANTS N \* Number of latches

VARIABLES mode, latchPawlPosition, motorStatus, secondaryReleaseStatus

\* Initial state of the system
Init == /\ mode = "RTC"
        /\ latchPawlPosition = "latched"
        /\ motorStatus = "operational"
        /\ secondaryReleaseStatus = "inactive"

\* Type invariant for the system
TypeOK == /\ mode \in {"RTC", "RTR", "secondaryRelease"}
          /\ latchPawlPosition \in {"latched", "unlatched"}
          /\ motorStatus \in {"operational", "failed"}
          /\ secondaryReleaseStatus \in {"inactive", "active"}

\* Problem invariant representing DDMR 26 requirement
DDMR26 == /\ (mode = "RTC" => latchPawlPosition = "latched")
          /\ (mode = "RTR" => latchPawlPosition = "unlatched")
          /\ (mode = "secondaryRelease" => secondaryReleaseStatus = "active")

\* Steps for nominal capture/release sequence
NominalCapture == /\ mode = "RTC"
                  /\ latchPawlPosition = "latched"
                  /\ motorStatus = "operational"
                  /\ mode' = "RTR"
                  /\ latchPawlPosition' = "unlatched"
                  /\ motorStatus' = motorStatus
                  /\ secondaryReleaseStatus' = secondaryReleaseStatus

NominalRelease == /\ mode = "RTR"
                  /\ latchPawlPosition = "unlatched"
                  /\ motorStatus = "operational"
                  /\ mode' = "RTC"
                  /\ latchPawlPosition' = "latched"
                  /\ motorStatus' = motorStatus
                  /\ secondaryReleaseStatus' = secondaryReleaseStatus

\* Steps for secondary release operation sequence
SecondaryRelease == /\ mode = "RTC"
                    /\ latchPawlPosition = "latched"
                    /\ motorStatus = "failed"
                    /\ secondaryReleaseStatus = "inactive"
                    /\ mode' = "secondaryRelease"
                    /\ latchPawlPosition' = latchPawlPosition
                    /\ motorStatus' = motorStatus
                    /\ secondaryReleaseStatus' = "active"

\* Next-state relation
Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, motorStatus, secondaryReleaseStatus>>

=============================================================================