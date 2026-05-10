----------------------------- MODULE AnomalyAlertModel -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT
    Devices,          (* Set of possible device identifiers, e.g., addresses *)
    EventTypes,       (* Set of possible event type strings *)
    EventRawData,     (* Set of possible raw event data (bytes) *)
    Timestamps,       (* Set of possible timestamp values (integers) *)
    Reporters,        (* Set of possible reporter addresses *)
    PossibleEventIDs  (* An abstract set representing all potential event IDs *)

ASSUME  IsFiniteSet(Devices) /\ Devices /= {}
        /\ IsFiniteSet(EventTypes) /\ EventTypes /= {}
        /\ IsFiniteSet(EventRawData) /\ EventRawData /= {}
        /\ IsFiniteSet(Timestamps) /\ Timestamps /= {}
        /\ IsFiniteSet(Reporters) /\ Reporters /= {}
        /\ IsFiniteSet(PossibleEventIDs) /\ PossibleEventIDs /= {}

(* Uninterpreted function to model event ID calculation *)
(* This abstracts keccak256(abi.encode(deviceId, detectionTimestamp, eventType, eventData)) *)
CalculateEventID(_device, _timestamp, _type, _data) ==
    CHOOSE id \in PossibleEventIDs : TRUE

(* Define the structure for a recorded anomaly event *)
AnomalyEvent == [eventId: PossibleEventIDs, deviceId: Devices, detectionTimestamp: Timestamps, eventType: EventTypes, eventData: EventRawData, reporter: Reporters]

VARIABLES
    hasAlertBeenTriggered, (* Mapping: EventID -> BOOLEAN *)
    recordedAnomalies,     (* Mapping: EventID -> AnomalyEvent record *)
    processedEventIds      (* Sequence of processed EventIDs *)

vars == <<hasAlertBeenTriggered, recordedAnomalies, processedEventIds>>

Init ==
    (* Initialize hasAlertBeenTriggered as a total function mapping all EventIDs to FALSE *)
    /\ hasAlertBeenTriggered = [id \in PossibleEventIDs |-> FALSE]
    (* Initialize recordedAnomalies as an empty partial function *)
    /\ recordedAnomalies = [id \in {} |-> [eventId: id, deviceId: 1, detectionTimestamp: 1, eventType: 1, eventData: 1, reporter: 1]]
    /\ processedEventIds = <<>>


ProcessAnomaly(d, ts, et, ed, rep) ==
    LET eventId == CalculateEventID(d, ts, et, ed) IN
       /\ ~hasAlertBeenTriggered[eventId]  (* Enabling condition: event not yet processed *)
       /\ hasAlertBeenTriggered' = [hasAlertBeenTriggered EXCEPT ![eventId] = TRUE]
       /\ recordedAnomalies' = recordedAnomalies @@ (eventId :> [
                                   eventId |-> eventId,
                                   deviceId |-> d,
                                   detectionTimestamp |-> ts,
                                   eventType |-> et,
                                   eventData |-> ed,
                                   reporter |-> rep
                               ])
       /\ processedEventIds' = Append(processedEventIds, eventId)


Next ==
    \E d \in Devices, ts \in Timestamps, et \in EventTypes, ed \in EventRawData, rep \in Reporters:
        ProcessAnomaly(d, ts, et, ed, rep)
    \/ UNCHANGED vars (* Allow stuttering for model completeness *)

Spec == Init /\ [][Next]_vars

(* ====== PROPERTIES - Invariants and Consistency Checks ====== *)

TypeOK ==
       /\ hasAlertBeenTriggered \in [PossibleEventIDs -> BOOLEAN]
       /\ \A id \in DOMAIN recordedAnomalies : recordedAnomalies[id] \in AnomalyEvent
       /\ processedEventIds \in Seq(PossibleEventIDs)


(* 
Idempotency: 
The system ensures that processing the same logical anomaly event multiple times does not lead to 
multiple records or inconsistent states. This is achieved in two main ways:
1. Action Guard: The `ProcessAnomaly` action has an enabling condition `~hasAlertBeenTriggered[eventId]`.
   This means if an event with a specific `eventId` has already been processed, the action to process it 
   again will not be enabled. This mirrors the `require(!hasAlertBeenTriggered[eventId])` in Solidity.
2. Uniqueness of Processed IDs: The `Consistency_ProcessedIdsAreUnique` invariant (defined below) checks 
   that every `eventId` in the `processedEventIds` sequence is unique. This confirms the outcome 
   of the idempotency mechanism.
*)

(* Data Consistency Invariants *)
Consistency_RecordedEventIdMatchesKey ==
    \A id \in DOMAIN recordedAnomalies :
        recordedAnomalies[id].eventId = id

Consistency_TriggeredImpliesRecorded ==
    \A id \in PossibleEventIDs :
        hasAlertBeenTriggered[id] => (id \in DOMAIN recordedAnomalies)

Consistency_RecordedImpliesTriggered ==
    \A id \in DOMAIN recordedAnomalies :
        hasAlertBeenTriggered[id]

Consistency_TriggeredInProcessedIds ==
    \A id \in PossibleEventIDs :
        hasAlertBeenTriggered[id] <=> (\E i \in 1..Len(processedEventIds) : processedEventIds[i] = id)

Consistency_ProcessedIdsAreUnique ==
    \A i,j \in 1..Len(processedEventIds) :
        (i /= j) => (processedEventIds[i] /= processedEventIds[j])

(* Optional: Liveness - If a new, valid anomaly is reported, it eventually gets processed. Requires fairness. *)
(* Liveness_EventualProcessing(d, ts, et, ed, rep) ==
    LET eventId == CalculateEventID(d, ts, et, ed) IN
    (~hasAlertBeenTriggered[eventId]) ~> hasAlertBeenTriggered[eventId] *)

=============================================================================
