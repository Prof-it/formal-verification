-------------------------------- MODULE Blockchain --------------------------------
EXTENDS Integers, Sequences, TLC, P2PNetwork, Nat

CONSTANTS Customers
VARIABLES ledger, contractStates, actions

(*--algorithm Blockchain
variables
  ledger = << >>,
  contractStates = [c \in Customers |-> "ready"],
  actions = << >>;

begin
  RecordAnomaly:
    either \E event \in alerts:
      event.type = "anomaly" ->
        ledger' := Append(ledger, event),
        contractStates' := contractStates,
        actions' := actions;

  TriggerContract:
    either \E entry \in ledger:
      entry.type = "anomaly" ->
        contractStates' := [contractStates EXCEPT ![entry.customerId] = "actioned"],
        actions' := Append(actions, ["pauseBilling", entry.customerId]),
        ledger' := ledger;

end algorithm; *)

Init == 
  /\ ledger = << >>
  /\ contractStates = [c \in Customers |-> "ready"]
  /\ actions = << >>
  /\ currentTime = 0

RecordAnomaly ==
  \E event \in alerts:
    event.type = "anomaly" /\
    ledger' = Append(ledger, event) /\
    contractStates' = contractStates /\
    actions' = actions /\
    currentTime' = currentTime + 1

TriggerContract ==
  \E entry \in ledger:
    entry.type = "anomaly" /\
    contractStates' = [contractStates EXCEPT ![entry.customerId] = "actioned"] /\
    actions' = Append(actions, ["pauseBilling", entry.customerId]) /\
    ledger' = ledger /\
    currentTime' = currentTime

Next == RecordAnomaly \/ TriggerContract

Spec == Init \/ [][Next]_<<ledger, contractStates, actions, currentTime>>

(* Properties *)
TypeOK == 
  ledger \in Seq([type: String, customerId: Customers]) /\
  contractStates \in [Customers -> {"ready", "actioned"}] /\
  actions \in Seq([String, Customers]) /\
  currentTime \in Nat

LedgerImmutability ==
  \A i \in 1..Len(ledger):
    \A j \in i..Len(ledger):
      ledger[i] = ledger[j]

ContractStateInvariant ==
  \A c \in Customers:
    contractStates[c] = "actioned" => \E entry \in ledger:
      entry.customerId = c /\ entry.type = "anomaly"

=============================================================================
