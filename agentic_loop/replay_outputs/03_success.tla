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

MotorDrive ==
    /\ updatePhase = "none"
    /\ motor = "stopped"
    /\ motor' = "driving"
    /\ updatePhase' = "motorPositionUpdate"
    /\ UNCHANGED <<striker, latch, nea, motorPosition>>

MotorStop ==
    /\ updatePhase = "none"
    /\ motor = "driving"
    /\ motor' = "stopped"
    /\ UNCHANGED <<striker, latch, motorPosition, nea, updatePhase>>

MotorFail ==
    /\ updatePhase = "none"
    /\ motor \in {"stopped", "driving"}
    /\ motor' = "failed"
    /\ UNCHANGED <<striker, latch, nea, motorPosition, updatePhase>>

ChangeMotorPosition ==
    /\ updatePhase = "motorPositionUpdate"
    /\ motor = "driving"
    /\ motorPosition' \in {"capture", "release"}
    /\ motorPosition' # motorPosition
    /\ updatePhase' = "latchUpdate"
    /\ UNCHANGED <<motor, striker, latch, nea>>

MotorChangesLatchPosition ==
    /\ updatePhase = "latchUpdate"
    /\ motor = "driving"
    /\ latch # motorPosition
    /\ latch' = motorPosition
    /\ updatePhase' = "none"
    /\ UNCHANGED <<motor, striker, nea, motorPosition>>

NeaChangesLatchPosition ==
    /\ updatePhase = "none"
    /\ nea = "fired"
    /\ latch' = "release"
    /\ UNCHANGED <<motor, striker, nea, motorPosition, updatePhase>>

StrikerToggle ==
    /\ updatePhase = "none"
    /\ striker' = ~striker
    /\ UNCHANGED <<motor, latch, nea, motorPosition, updatePhase>>

NeaFire ==
    /\ updatePhase = "none"
    /\ striker
    /\ nea = "ready"
    /\ motor = "failed"
    /\ nea' = "fired"
    /\ UNCHANGED <<motor, latch, striker, motorPosition, updatePhase>>

Next ==
    \/ MotorDrive
    \/ MotorStop
    \/ MotorFail
    \/ ChangeMotorPosition
    \/ MotorChangesLatchPosition
    \/ NeaChangesLatchPosition
    \/ StrikerToggle
    \/ NeaFire

DDMR26 == updatePhase = "none" => latch = motorPosition

Spec == Init /\ [][Next]_<<motor, striker, latch, nea, motorPosition, updatePhase>>

=============================================================================
