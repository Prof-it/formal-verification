---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS NDS_COUNT, DOCKING_LIMIT

VARIABLES latchMode, latchPosition, motorStatus, secondaryReleaseStatus

\* Latch modes
ReadyToCapture == "RTC"
ReadyToRelease == "RTR"
SecondaryRelease == "SR"

\* Motor status
MotorOperational == "Operational"
MotorFailed == "Failed"

\* Secondary release status
SecondaryInactive == "Inactive"
SecondaryActive == "Active"

Init == /\ latchMode \in {ReadyToCapture, ReadyToRelease, SecondaryRelease}
        /\ latchPosition \in 0..100 \* Position range from 0 to 100
        /\ motorStatus \in {MotorOperational, MotorFailed}
        /\ secondaryReleaseStatus \in {SecondaryInactive, SecondaryActive}

TypeOK == /\ latchMode \in {ReadyToCapture, ReadyToRelease, SecondaryRelease}
          /\ latchPosition \in 0..100
          /\ motorStatus \in {MotorOperational, MotorFailed}
          /\ secondaryReleaseStatus \in {SecondaryInactive, SecondaryActive}

\* Direct indication of critical states
DDMR26 == /\ (latchMode = ReadyToCapture \/ latchMode = ReadyToRelease \/ latchMode = SecondaryRelease)
          /\ (motorStatus = MotorOperational \/ motorStatus = MotorFailed)
          /\ (secondaryReleaseStatus = SecondaryInactive \/ secondaryReleaseStatus = SecondaryActive)

\* Nominal operation steps
NominalCapture == /\ latchMode = ReadyToCapture
                  /\ latchPosition = 0
                  /\ motorStatus = MotorOperational
                  /\ latchMode' = ReadyToRelease
                  /\ latchPosition' = 100

NominalRelease == /\ latchMode = ReadyToRelease
                  /\ latchPosition = 100
                  /\ motorStatus = MotorOperational
                  /\ latchMode' = ReadyToCapture
                  /\ latchPosition' = 0

\* Secondary release operation
SecondaryReleaseOp == /\ latchMode = ReadyToCapture
                      /\ latchPosition = 0
                      /\ motorStatus = MotorFailed
                      /\ secondaryReleaseStatus = SecondaryInactive
                      /\ secondaryReleaseStatus' = SecondaryActive
                      /\ latchMode' = SecondaryRelease

Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryReleaseOp

Spec == Init /\ [][Next]_<<latchMode, latchPosition, motorStatus, secondaryReleaseStatus>>

=========================================================================
Ensure DDMR26 evaluates to a boolean by correcting the logical conditions.
====