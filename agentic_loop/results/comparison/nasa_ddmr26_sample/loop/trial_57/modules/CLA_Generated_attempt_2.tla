---- MODULE CLA_Generated_attempt_2 ----
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

\* Problem invariant representing the requirement for direct indication of critical states
DDMR26 == \A i \in 1..N: 
            IF mode[i] = "RTC" THEN latchPawlPosition[i] = "unlatched"
            ELSE IF mode[i] = "RTR" THEN latchPawlPosition[i] = "latched"
            ELSE secondaryReleaseActivated[i] = TRUE

\* Steps representing the nominal and secondary release operations
NominalCapture == /\ \E i \in 1..N: mode[i] = "RTC" /\ latchPawlPosition[i] = "unlatched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "latched"]
                  /\ UNCHANGED <<mode, secondaryReleaseActivated>>

NominalRelease == /\ \E i \in 1..N: mode[i] = "RTR" /\ latchPawlPosition[i] = "latched"
                  /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                  /\ UNCHANGED <<mode, secondaryReleaseActivated>>

SecondaryRelease == /\ \E i \in 1..N: mode[i] = "RTC" /\ secondaryReleaseActivated[i] = FALSE
                     /\ secondaryReleaseActivated' = [secondaryReleaseActivated EXCEPT ![i] = TRUE]
                     /\ mode' = [mode EXCEPT ![i] = "SecondaryRelease"]
                     /\ latchPawlPosition' = [latchPawlPosition EXCEPT ![i] = "unlatched"]
                     /\ UNCHANGED <<latchPawlPosition>>

Next == NominalCapture \/ NominalRelease \/ SecondaryRelease

\* Specification of the system
Spec == Init /\ [][Next]_<<mode, latchPawlPosition, secondaryReleaseActivated>>

=====================================================================
Define missing recursive function as bracket-domain.
====