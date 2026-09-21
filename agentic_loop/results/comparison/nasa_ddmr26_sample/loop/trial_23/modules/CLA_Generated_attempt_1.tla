---- MODULE CLA_Generated_attempt_1 ----
EXTENDS Naturals, Sequences

CONSTANTS LATCH_COUNT

VARIABLES latchMode, latchPosition, latchState

\* Latch modes
ReadyToCapture == 0
ReadyToRelease == 1
SecondaryRelease == 2

\* Latch states
Latched == "Latched"
Unlatched == "Unlatched"
Failed == "Failed"

Init == /\ latchMode \in 0..2
        /\ latchPosition \in 0..LATCH_COUNT
        /\ latchState \in [0..LATCH_COUNT -> {Latched, Unlatched, Failed}]

TypeOK == /\ latchMode \in 0..2
          /\ latchPosition \in 0..LATCH_COUNT
          /\ latchState \in [0..LATCH_COUNT -> {Latched, Unlatched, Failed}]

\* Direct indication of critical states
DDMR26 == \A i \in 0..LATCH_COUNT: 
            IF latchMode = SecondaryRelease THEN latchState[i] = Failed
            ELSE IF latchMode = ReadyToCapture THEN latchState[i] = Latched
            ELSE latchState[i] = Unlatched

Next == \E i \in 0..LATCH_COUNT:
          /\ latchMode' \in 0..2
          /\ latchPosition' \in 0..LATCH_COUNT
          /\ latchState' = [latchState EXCEPT ![i] = 
                IF latchMode' = SecondaryRelease THEN Failed
                ELSE IF latchMode' = ReadyToCapture THEN Latched
                ELSE Unlatched]

Spec == Init /\ [][Next]_<<latchMode, latchPosition, latchState>>

=========================================================================
Ensure DDMR26 evaluates to a boolean by correcting the logical conditions.
Ensure DDMR26 evaluates to a boolean by correcting the logical conditions.
====