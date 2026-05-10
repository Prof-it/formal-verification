-------------------------- MODULE MainCheckRefinement --------------------------
EXTENDS AnomalyAlertModel, Sequences

(*
Refinement view over implementation state.
This keeps the current implementation model unchanged and adds explicit mapping
operators plus proof-style invariants that can be checked by TLC.
*)

Mapped_ledger ==
    [i \in 1..Len(processedEventIds) |->
        LET e == processedEventIds[i] IN
            IF e \in DOMAIN recordedAnomalies
            THEN [type |-> recordedAnomalies[e].eventType,
                  deviceId |-> recordedAnomalies[e].deviceId]
            ELSE [type |-> CHOOSE et \in EventTypes : TRUE,
                  deviceId |-> CHOOSE d \in Devices : TRUE]
    ]

Mapped_states ==
    [d \in Devices |->
        IF \E e \in DOMAIN recordedAnomalies :
            recordedAnomalies[e].deviceId = d /\ hasAlertBeenTriggered[e]
        THEN "actioned" ELSE "ready"
    ]

Mapped_actions ==
    [i \in 1..Len(processedEventIds) |->
        LET e == processedEventIds[i] IN
            IF e \in DOMAIN recordedAnomalies
            THEN <<"pauseBilling", recordedAnomalies[e].deviceId>>
            ELSE <<"pauseBilling", CHOOSE d \in Devices : TRUE>>
    ]

MappedAbsState == <<Mapped_ledger, Mapped_states, Mapped_actions>>

(* Hidden assumptions discussed in the paper. *)
Uniq ==
    \A i,j \in 1..Len(processedEventIds) :
        (i /= j) => (processedEventIds[i] /= processedEventIds[j])

Cons ==
    \A e \in DOMAIN recordedAnomalies : hasAlertBeenTriggered[e]

Causality ==
    \A i \in 1..Len(processedEventIds) :
        LET e == processedEventIds[i] IN
            e \in DOMAIN recordedAnomalies /\ hasAlertBeenTriggered[e]

(* Init-style refinement obligation encoded as a state predicate implication. *)
InitRefinement ==
    (processedEventIds = <<>>) =>
        (/\ Len(Mapped_ledger) = 0
         /\ Len(Mapped_actions) = 0
         /\ \A d \in Devices : Mapped_states[d] = "ready")

(* Step-style correspondence encoded as state-level consistency relation. *)
StepRefinement ==
    /\ Len(Mapped_ledger) = Len(processedEventIds)
    /\ Len(Mapped_actions) = Len(processedEventIds)
    /\ \A i \in 1..Len(processedEventIds) :
          LET e == processedEventIds[i] IN
            /\ e \in DOMAIN recordedAnomalies
            /\ Mapped_ledger[i].type = recordedAnomalies[e].eventType
            /\ Mapped_ledger[i].deviceId = recordedAnomalies[e].deviceId
            /\ Mapped_actions[i][1] = "pauseBilling"
            /\ Mapped_actions[i][2] = recordedAnomalies[e].deviceId

(* Composite claim: refinement is conditional on hidden assumptions. *)
RefinementUnderAssumptions == (Uniq /\ Cons /\ Causality) => StepRefinement

=============================================================================
