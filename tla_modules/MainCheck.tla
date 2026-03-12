-------------------------- MODULE MainCheck --------------------------
EXTENDS RefinementMapping

(* Create named instances for clarity in this module *)
I == INSTANCE Impl
A == INSTANCE Abs

R == INSTANCE RefinementMapping (* To access R!InitRefinement and R!StepRefinement *)

(* The specification TLC will run is the implementation's specification *)
Spec == I!Spec

(* Re-export invariants from Impl to check them during refinement. *)
(* These properties will be listed as INVARIANTS in MainCheck.cfg. *)
ImplTypeOK                               == I!TypeOK
Consistency_RecordedEventIdMatchesKey      == I!Consistency_RecordedEventIdMatchesKey
Consistency_TriggeredImpliesRecorded     == I!Consistency_TriggeredImpliesRecorded
Consistency_RecordedImpliesTriggered     == I!Consistency_RecordedImpliesTriggered
Consistency_TriggeredInProcessedIds      == I!Consistency_TriggeredInProcessedIds
Consistency_ProcessedIdsAreUnique        == I!Consistency_ProcessedIdsAreUnique

=============================================================================
