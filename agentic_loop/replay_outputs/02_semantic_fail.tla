------------------------------ MODULE CLA_Generated ------------------------------
EXTENDS Integers

VARIABLES motor, striker, latch, nea, motorPosition, updatePhase

TypeOK ==
    /\ motor \in {"driving", "stopped", "failed"}
    /\ striker \in BOOLEAN
    /\ latch \in {"capture", "release"}
    /\ nea \in {"ready", "fired"}
    /\ motorPosition \in {"capture", "release"}
    /\ updatePhase \in {"none", "motorPositionUpdate", "latchUpdate"}

Init ==
    /\ motor = "stopped"
    /\ striker = FALSE
    /\ latch = "capture"
    /\ nea = "ready"
    /\ motorPosition = "capture"
    /\ updatePhase = "none"

Next ==
    /\ motor' = motor
    /\ striker' = striker
    /\ latch' = latch
    /\ nea' = nea
    /\ motorPosition' = motorPosition
    /\ updatePhase' = updatePhase

\* Intentional semantic issue for repair stage
DDMR26 == updatePhase = "none" => UnknownOp(latch, motorPosition)

Spec == Init /\ [][Next]_<<motor, striker, latch, nea, motorPosition, updatePhase>>

=============================================================================
