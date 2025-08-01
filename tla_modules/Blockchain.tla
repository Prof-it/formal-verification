-------------------------------- MODULE Blockchain --------------------------------
EXTENDS Integers, Sequences, TLC, Naturals

CONSTANTS Customers
VARIABLES ledger, contractStates, actions
EventTypesStrings == {"anomaly", "pauseBilling"}
States == {"ready", "actioned"}

Init == 
  /\ ledger = << >>
  /\ contractStates = [c \in Customers |-> "ready"]
  /\ actions = << >>

RecordAnomaly(customer, eventTypeStr) == 
    /\ eventTypeStr = "anomaly"
    /\ ledger' = Append(ledger, [type |-> eventTypeStr, customerId |-> customer])
    /\ UNCHANGED <<contractStates, actions>>

TriggerContract ==
  \E i \in 1..Len(ledger):
    /\ ledger[i].type = "anomaly"
    /\ contractStates' = [contractStates EXCEPT ![ledger[i].customerId] = "actioned"]
    /\ actions' = Append(actions, [type |->  "pauseBilling", customerId |->  ledger[i].customerId])
    /\ ledger' = ledger

Next ==
    (\E c \in Customers, etStr \in EventTypesStrings: RecordAnomaly(c, etStr))
    \/ TriggerContract

vars == <<ledger, contractStates, actions>>
Spec == Init /\ [][Next]_vars

(* Properties *)
TypeOK == 
  /\ ledger \in Seq([type: {"ready", "actioned"}, customerId: Customers]) 
  /\ contractStates \in [Customers -> States ]
  /\ actions \in Seq([type: {"ready", "actioned"}, customerId: Customers])

LedgerImmutability ==
  \A i \in 1..Len(ledger):
    \A j \in i..Len(ledger):
      ledger[i] = ledger[j]

ContractStateInvariant ==
  \A c \in Customers:
    contractStates[c] = "actioned" 
            => \E i \in 1..Len(ledger):
                ledger[i].customerId = c /\ ledger[i].type = "anomaly"


=============================================================================
(* Renamed to avoid clash, parameterized *)
    (* Action is only enabled if eventTypeStr is "anomaly" and leads to a state change. *)
    (* Otherwise, this specific action instance is disabled. *)