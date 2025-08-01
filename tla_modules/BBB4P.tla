------------------------------- MODULE BBB4P -------------------------------
EXTENDS Naturals, Sequences

CONSTANT QuantumStates, CurrentTimestamp

VARIABLES aliceState, bobState, channelState, qubitState, 
          qubitLocation, eveInterfered, transferred, auditTrail

Init ==   /\ aliceState = "hasQubit"
          /\ bobState = "waiting"
          /\ channelState = "ready"
          /\ qubitState \in QuantumStates
          /\ qubitLocation = "alice"
          /\ eveInterfered = FALSE
          /\ transferred = FALSE
          /\ auditTrail = << >>

PrepareEntanglement ==
  /\ aliceState = "hasQubit" /\ channelState = "ready"
  /\ channelState' = "entangled"
  /\ UNCHANGED <<aliceState, bobState, qubitState, qubitLocation, transferred, eveInterfered, auditTrail>>

TeleportQubit ==
  /\ channelState = "entangled" /\ aliceState = "hasQubit"
  /\ aliceState' = "sent"
  /\ channelState' = "used"
  /\ qubitLocation' = "inChannel"
  /\ transferred' = TRUE
  /\ UNCHANGED <<bobState, qubitState, eveInterfered, auditTrail>>

ReceiveAtBob ==
  /\ transferred = TRUE /\ qubitLocation = "inChannel" /\ bobState = "waiting"
  /\ bobState' = "received"
  /\ qubitLocation' = "bob"
  /\ auditTrail' = Append(auditTrail, [type |-> "BB4P-transfer", time |-> CurrentTimestamp])
  /\ UNCHANGED <<aliceState, qubitState, channelState, eveInterfered, transferred>>

Eavesdrop ==
  /\ qubitLocation = "inChannel" /\ eveInterfered = FALSE
  /\ eveInterfered' = TRUE
  /\ qubitLocation' = "eavesdropper"
  /\ qubitState' = "collapsed" \* Qubit is destroyed
  /\ channelState' = "tampered"
  /\ UNCHANGED <<aliceState, bobState, auditTrail, transferred>>

Next == PrepareEntanglement \/ TeleportQubit \/ ReceiveAtBob \/ Eavesdrop  

Spec == Init /\ [][Next]_<<aliceState, bobState, channelState, qubitState, qubitLocation, eveInterfered, transferred, auditTrail>>
    
NoCloning == qubitLocation \in {"alice", "bob", "inChannel", "eavesdropper", "lost"}

NoUndetectableEavesdropping == eveInterfered = TRUE => qubitState = "collapsed"

Correctness == bobState = "received" 
                  => /\ qubitState # "collapsed"
                     /\ qubitLocation = "bob"
                     /\ channelState = "used"
BB4PTransfers(trail) == { t \in trail : t.type = "BB4P-transfer" }

ExactlyOneAudit == Len(BB4PTransfers(auditTrail)) = 1

INVARIANTS == 
  /\ NoCloning
  /\ NoUndetectableEavesdropping
  /\ Correctness
  /\ ExactlyOneAudit
=============================================================================
  (*
  aliceState,      \* "hasQubit", "sent"
  bobState,        \* "waiting", "received"
  channelState,    \* "ready", "entangled", "used", "tampered"
  qubitState,      \* current quantum state (symbolic)
  qubitLocation,   \* "alice", "bob", "inChannel", "eavesdropper", "lost"
  eveInterfered,   \* TRUE if Eve tried to intercept
  transferred,     \* TRUE after teleportation step
  auditTrail       \* Sequence of audit entries
  *)

\* Modification History
\* Last modified Fri Aug 01 05:46:55 CEST 2025 by tianxiang.lu
\* Created Fri Aug 01 05:18:36 CEST 2025 by tianxiang.lu
