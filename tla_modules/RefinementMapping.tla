-------------------------- MODULE RefinementMapping --------------------------
EXTENDS AnomalyAlertModel, Blockchain

Impl == INSTANCE AnomalyAlertModel
Abs == INSTANCE Blockchain

(* Define how Abstract Spec (Abs) variables are derived from Impl variables *)

(* Assumption: Abs.Customers is the same set as Impl.Devices *)
(* Assumption: Abs.EventTypesStrings is compatible with Impl.EventTypes (e.g., Impl.EventTypes contains "anomaly") *)

Mapped_ledger(recordedAnomalies_i, processedEventIds_i) ==
    LET MapEvent(eventRecord) == [type |-> eventRecord.eventType, customerId |-> eventRecord.deviceId]
    IN [idx \in 1..Len(processedEventIds_i) |-> MapEvent(recordedAnomalies_i[processedEventIds_i[idx]])]

Mapped_contractStates(hasAlertBeenTriggered_i, recordedAnomalies_i, allDevices_i) ==
    [dev \in allDevices_i |->
        IF \E id \in DOMAIN recordedAnomalies_i:
            (* Check if any anomaly for this device has been recorded and triggered *)
            /\ recordedAnomalies_i[id].deviceId = dev
            /\ hasAlertBeenTriggered_i[id]
        THEN "actioned"
        ELSE "ready"]

(* The 'actions' variable in Blockchain.tla logs specific actions like "pauseBilling".
   AnomalyAlertModel.tla doesn't directly create these. 
   If AlertTriggered in Impl implies such an action, we can map it.
   Otherwise, for refinement, we'd expect Impl steps to leave Abs.actions UNCHANGED mostly. 
   This mapping assumes each processed anomaly implies a "pauseBilling" action. *)
Mapped_actions(recordedAnomalies_i, processedEventIds_i) ==
    LET MapAction(eventRecord) == <<"pauseBilling", eventRecord.deviceId>>
    IN [idx \in 1..Len(processedEventIds_i) |-> MapAction(recordedAnomalies_i[processedEventIds_i[idx]])]



(* Refinement Theorem Formulation for TLC Checking *)

(* This defines the state of the abstract spec based on the implementation's state. *)
MappedAbsState(impl_vars_record) ==
  [ ledger         |-> Mapped_ledger(impl_vars_record.recordedAnomalies, impl_vars_record.processedEventIds),
    contractStates |-> Mapped_contractStates(impl_vars_record.hasAlertBeenTriggered, impl_vars_record.recordedAnomalies, Impl!Devices), 
    actions        |-> Mapped_actions(impl_vars_record.recordedAnomalies, impl_vars_record.processedEventIds)
  ]

(* Check that the initial state of the implementation, when mapped, satisfies the initial state of the abstract spec. *)
InitRefinement == Impl!Init => 
    LET currentImplVars == [v \in DOMAIN Impl!vars |-> Impl!vars[v]]
        currentAbsState == MappedAbsState(currentImplVars)
    IN Abs!Init /. currentAbsState

(* Check that every step of the implementation, when mapped, corresponds to a valid step of the abstract spec or a stuttering step. *)
StepRefinement ==
    Impl!Next =>
        LET currentImplStateRec == [v \in DOMAIN Impl!vars |-> Impl!vars[v]]
            nextImplStateRec    == [v \in DOMAIN Impl!vars |-> Impl!vars'[v]]
            
            abs_state        == MappedAbsState(currentImplStateRec)
            abs_state_prime  == MappedAbsState(nextImplStateRec)
        IN
            \/ Abs!Next /. [ Abs!ledger         |-> abs_state.ledger,
                             Abs!contractStates |-> abs_state.contractStates,
                             Abs!actions        |-> abs_state.actions,
                             Abs!ledger'        |-> abs_state_prime.ledger,
                             Abs!contractStates'|-> abs_state_prime.contractStates,
                             Abs!actions'       |-> abs_state_prime.actions
                           ]
            \/ (abs_state_prime = abs_state) (* Abstract stuttering step *)

(* Overall Refinement Theorem (conceptual) - TLC checks InitRefinement and StepRefinement separately or via a combined property. *)
(* THEOREM Impl!Spec => Abs!Spec THEOREM Impl!Spec => Abs!Spec(Mapped_ledger(...)/ledger, ...) *) 

=============================================================================
