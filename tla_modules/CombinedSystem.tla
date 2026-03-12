-------------------------- MODULE CombinedSystem --------------------------
EXTENDS TLC, Naturals, Integers, Sequences, Strings, FiniteSets

(* Module Instantiations *)
EM == INSTANCE EnergyMeter
P2P == INSTANCE P2PNetwork
BC == INSTANCE Blockchain

vars == << EM!vars, P2P!vars, BC!vars >>

Init == EM!Init /\ P2P!Init /\ BC!Init

(* Action 1a: EnergyMeter's SensorMeasureAnomaly occurs independently *)
EM_SensorMeasureAnomaly == 
    /\ EM!SensorMeasureAnomaly
    /\ UNCHANGED <<P2P!vars, BC!vars>>

(* Action 1b: EnergyMeter's SensorReportAnomaly occurs independently *)
EM_SensorReportAnomaly == 
    /\ EM!SensorReportAnomaly
    /\ UNCHANGED <<P2P!vars, BC!vars>>

(* Action 1c: EnergyMeter controller processes events and sends info to P2P *)
EM_Controller_Processes_And_Sends_To_P2P ==
    /\ EM!events /= << >> (* Precondition: events are available in EnergyMeter *)
    /\ (LET eventPayload == Head(EM!events) IN (* For simplicity, take the first event string as payload, e.g., "anomaly_detected: s1" *)
                                          (* A more robust model might parse the sensor ID from this string *)
            (* EM variable changes - ControllerProcessAnomaly clears events *)
        /\ ( /\ EM!events' = << >> 
             /\ EM!sensorStates' = EM!sensorStates
           )

        /\ ( (* P2P variable changes for SendAlert *) 
             /\ P2P!messages' = Append(P2P!messages, [ src |-> P2P!ControllerNode, 
                                                        dest |-> P2P!AuthorityNode, 
                                                        type |-> "alert", 
                                                        data |-> eventPayload
                                                      ])
             /\ P2P!alerts' = P2P!alerts (* UNCHANGED P2P!alerts from P2P!SendAlert definition *)
           )

        /\ ( (* Blockchain variables unchanged *) 
             BC!vars' = BC!vars
           )
       )


(* Action 2: P2P AuthorityNode delivers a message internally (from P2P!messages to P2P!alerts) *)
P2P_Authority_Delivers_Message ==
    /\ \E msg \in P2P!messages:
        /\ msg.dest = P2P!AuthorityNode
        (* P2P variable changes for Deliver *)
        /\ P2P!alerts'   = P2P!alerts \cup {msg}
        /\ P2P!messages' = P2P!RemoveElement(P2P!messages, msg)

    (* EM and BC variables unchanged *)
    /\ EM!vars' = EM!vars
    /\ BC!vars'  = BC!vars

(* Action 3: Authority Node (using info from P2P!alerts) triggers a Blockchain RecordAnomaly action *)
Authority_Triggers_Blockchain_Record ==
    /\ \E alert_msg \in P2P!alerts: (* An alert has been delivered to the authority *)
        LET p2pPayload == alert_msg.data IN (* This is the string like "anomaly_detected: s1" *)
        (* Simplification: Assume the payload string itself can be used or parsed for customerId.
           For now, let's assume the string contains the sensor ID which is the customerId.
           A more robust model would parse this. If p2pPayload is "anomaly_detected: s1", customerId is "s1".
           Let's assume BC!RecordAnomaly can take the raw p2pPayload as customerId for now, 
           or we extract it. For minimal change, let's pass a fixed eventType. *)
        LET customerIdFromPayload == IF "anomaly_detected: " \subseteq p2pPayload 
                                     THEN SubSeq(p2pPayload, Len("anomaly_detected: ") + 1, Len(p2pPayload)) 
                                     ELSE "unknown_sensor" IN
        /\ customerIdFromPayload # "unknown_sensor" (* Ensure we got a sensor ID *)

        (* BC variable changes for RecordAnomaly *)
        /\ BC!ledger' = Append(BC!ledger, [type |-> "anomaly", customerId |-> customerIdFromPayload])
        /\ BC!contractStates' = BC!contractStates (* UNCHANGED from BC!RecordAnomaly def *)
        /\ BC!actions' = BC!actions             (* UNCHANGED from BC!RecordAnomaly def *)

        (* P2P state change: alert is now processed from P2P!alerts *)
        /\ P2P!alerts' = P2P!alerts \ {alert_msg}
        /\ P2P!messages' = P2P!messages (* UNCHANGED P2P!messages *)

        (* EM variables unchanged *)
        /\ EM!vars' = EM!vars

(* Action 4: Blockchain's independent TriggerContract action *)
BC_Independent_TriggerContract ==
    /\ \E entry \in BC!ledger:
        /\ entry.type = "anomaly"
        (* BC variable changes *) 
        /\ BC!contractStates' = [BC!contractStates EXCEPT ![entry.customerId] = "actioned"]
        /\ BC!actions' = Append(BC!actions, ["pauseBilling", entry.customerId])
        /\ BC!ledger' = BC!ledger
    
    (* EM and P2P variables unchanged *)
    /\ EM!vars' = EM!vars
    /\ P2P!vars' = P2P!vars


CombinedNext ==
    \/ EM_SensorMeasureAnomaly
    \/ EM_SensorReportAnomaly
    \/ EM_Controller_Processes_And_Sends_To_P2P
    \/ P2P_Authority_Delivers_Message
    \/ Authority_Triggers_Blockchain_Record
    \/ BC_Independent_TriggerContract

Spec == Init /\ [][CombinedNext]_vars

=============================================================================
