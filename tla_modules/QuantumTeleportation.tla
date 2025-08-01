-------------------------------- MODULE QuantumTeleportation --------------------------------

EXTENDS Sequences, Naturals
CONSTANTS TrustedParties, CurrentTimestamp
VARIABLES aliceStates, bobStates, channelStates, transferred, auditTrails


Init == 
  /\ aliceStates = [p \in TrustedParties |-> "hasQubit"] 
  /\ bobStates = [p \in TrustedParties |-> "waiting"] 
  /\ channelStates = [p \in TrustedParties |-> "ready"] 
  /\ transferred = FALSE
  /\ auditTrails = << >>

PrepareEntanglement ==
  \E p \in TrustedParties:
    /\ aliceStates[p] = "hasQubit" /\ channelStates[p] = "ready" 
    /\ channelStates' = [channelStates EXCEPT ![p] = "entangled"]
    /\ aliceStates' = aliceStates
    /\ bobStates' = bobStates
    /\ transferred' = FALSE
    /\ UNCHANGED auditTrails

TeleportQubit ==
  \E p \in TrustedParties:
    /\ channelStates[p] = "entangled" /\ aliceStates[p] = "hasQubit"
    /\ aliceStates' = [aliceStates EXCEPT ![p] = "sent"]
    /\ channelStates' = [channelStates EXCEPT ![p] = "used"]
    /\ transferred' = TRUE
    /\ UNCHANGED <<auditTrails, bobStates>>

ReceiveAtBob ==
  \E p \in TrustedParties:
    /\ transferred = TRUE /\ bobStates[p] = "waiting" 
    /\ bobStates' = [bobStates EXCEPT ![p] = "received"]
    /\ auditTrails' = Append(auditTrails, [type |-> "BB4P-transfer", time |-> CurrentTimestamp])
    /\ UNCHANGED <<transferred, channelStates, aliceStates>>

Next == PrepareEntanglement \/ TeleportQubit \/ ReceiveAtBob

Spec == Init \/ [][Next]_<<aliceStates, bobStates, channelStates, transferred, auditTrails>>

(* Properties *)
TypeOK == 
  /\ aliceStates \in [TrustedParties -> {"hasQubit", "sent"}] 
  /\ bobStates \in [TrustedParties -> {"waiting", "received"}]
  /\ channelStates \in [TrustedParties -> {"ready", "entangled", "used"}]
  /\ transferred \in BOOLEAN
  /\ auditTrails \in Seq([type: {"BB4P-transfer"}, time: Nat])

TeleportationIntegrity ==
  \A p \in TrustedParties:
    bobStates[p] = "received" => transferred = TRUE

AuditTrailCompleteness ==
  transferred = TRUE => \E t \in auditTrails:
    t[1] = "BB4P-transfer"

=============================================================================
