---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS N \* Number of latches

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
            ELSE IF mode[i] = "RTR" THEN latchPawlPosition[i] = "latched"
            ELSE IF mode[i] = "SecondaryRelease" THEN secondaryReleaseActivated[i] = TRUE

\* Steps representing the nominal and secondary release sequences
NominalCapture == /\ \E i \in 1..N: mode[i] = "RTC"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                  /\ mode' = [mode EXCEPT ![i] = "RTR"]

NominalRelease == /\ \E i \in 1..N: mode[i] = "RTR"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                  /\ mode' = [mode EXCEPT ![i] = "RTC"]

SecondaryRelease == /\ \E i \in 1..N: mode[i] = "RTC"
                    /\ secondaryReleaseActivated' = [secondaryReleaseActivated EXCEPT ![i] = TRUE]
                    /\ mode' = [mode EXCEPT ![i] = "SecondaryRelease"]

\* Next-state relation
Next == \/ NominalCapture
        \/ NominalRelease
        \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, secondaryReleaseActivated>>

=========================================================================
Ensure all IF-THEN-ELSE structures are properly closed with an ELSE clause.
====