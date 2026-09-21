---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANT N \* Number of latches

VARIABLES mode, latchPawlPosition, secondaryReleaseActivated

\* Initial state of the system
Init == /\ mode = [i \in 1..N |-> "RTC"]
        /\ latchPawlPosition = [i \in 1..N |-> "unlatched"]
        /\ secondaryReleaseActivated = [i \in 1..N |-> FALSE]

\* Type invariant for the system
TypeOK == /\ mode \in [1..N -> {"RTC", "RTR", "SecondaryRelease"}]
          /\ latchPawlPosition \in [1..N -> {"latched", "unlatched"}]
          /\ secondaryReleaseActivated \in [1..N -> BOOLEAN]

\* Problem invariant representing DDMR 26 requirement
DDMR26 == \A i \in 1..N: 
            IF mode[i] = "RTC" THEN latchPawlPosition[i] = "unlatched"
            ELSE IF mode[i] = "RTR" THEN latchPawlPosition[i] = "unlatched"
            ELSE IF mode[i] = "SecondaryRelease" THEN latchPawlPosition[i] = "unlatched"

\* Steps representing the nominal and secondary release sequences
NominalCapture == /\ \E i \in 1..N: mode[i] = "RTC"
                  /\ latchPawlPosition[i] = "unlatched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                  /\ UNCHANGED <<mode, secondaryReleaseActivated>>

NominalRelease == /\ \E i \in 1..N: mode[i] = "RTR"
                  /\ latchPawlPosition[i] = "latched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                  /\ UNCHANGED <<mode, secondaryReleaseActivated>>

SecondaryRelease == /\ \E i \in 1..N: mode[i] = "RTC" /\ secondaryReleaseActivated[i] = TRUE
                     /\ latchPawlPosition[i] = "latched"
                     /\ mode' = [mode EXCEPT ![i] = "SecondaryRelease"]
                     /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                     /\ UNCHANGED secondaryReleaseActivated

Next == NominalCapture \/ NominalRelease \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, secondaryReleaseActivated>>

=========================================================================
Ensure all IF-THEN-ELSE structures are properly closed with an ELSE clause.
====