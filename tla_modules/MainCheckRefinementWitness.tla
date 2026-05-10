---------------------- MODULE MainCheckRefinementWitness ----------------------
EXTENDS MainCheckRefinement, Sequences, FiniteSets

(*
Witness module: deliberately introduces a replay transition to produce
counterexamples for hidden-assumption breakdown claims.
*)

ReplayExistingProcessedEvent ==
    /\ Len(processedEventIds) > 0
    /\ \E i \in 1..Len(processedEventIds):
         LET replayId == processedEventIds[i] IN
           /\ replayId \in PossibleEventIDs
           /\ hasAlertBeenTriggered' = hasAlertBeenTriggered
           /\ recordedAnomalies' = recordedAnomalies
           /\ processedEventIds' = Append(processedEventIds, replayId)

NextWitness == Next \/ ReplayExistingProcessedEvent
SpecWitness == Init /\ [][NextWitness]_vars

(* Breakdown witnesses for paper claims *)
OneToOneProcessedToRecorded == Len(processedEventIds) = Cardinality(DOMAIN recordedAnomalies)

NoReplayInProcessedIds ==
    \A i,j \in 1..Len(processedEventIds) :
        (i /= j) => (processedEventIds[i] /= processedEventIds[j])

(* If replay happens, this can fail even when type safety still holds. *)
RefinementBreakdownWitness == OneToOneProcessedToRecorded /\ NoReplayInProcessedIds

=============================================================================
