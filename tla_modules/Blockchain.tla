EXTENDS Integers, Sequences, TLC, P2PNetwork

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
  ledger = << >> /\
  contractStates = [c \in Customers |-> "ready"] /\
  actions = << >>

RecordAnomaly ==
  \E event \in alerts:
    event.type = "anomaly" /\
    ledger' = Append(ledger, event) /\
    contractStates' = contractStates /\
    actions' = actions

TriggerContract ==
  \E entry \in ledger:
    entry.type = "anomaly" /\
    contractStates' = [contractStates EXCEPT ![entry.customerId] = "actioned"] /\
    actions' = Append(actions, ["pauseBilling", entry.customerId]) /\
    ledger' = ledger

Next == RecordAnomaly \/ TriggerContract

Spec == Init \/ [][Next]_<<ledger, contractStates, actions>>

(* Properties *)
TypeOK == 
  ledger \in Seq([type: String, customerId: Customers]) /\
  contractStates \in [Customers -> {"ready", "actioned"}] /\
  actions \in Seq([String, Customers])

LedgerImmutability ==
  \A i \in 1..Len(ledger):
    \A j \in i..Len(ledger):
      ledger[i] = ledger[j]

ContractStateInvariant ==
  \A c \in Customers:
    contractStates[c] = "actioned" => \E entry \in ledger:
      entry.customerId = c /\ entry.type = "anomaly"
