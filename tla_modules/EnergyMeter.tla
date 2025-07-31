-------------------------------- MODULE EnergyMeter --------------------------------
EXTENDS Integers, Sequences, TLC 
CONSTANTS Sensors, MaxEvents 
VARIABLES sensorStates, events 

Init == /\ sensorStates = [s \in Sensors |-> "normal"] 
        /\ events = << >>

(* Actions:  *)
SensorReportAnomaly == \E s \in Sensors: 
                            /\ sensorStates[s] = "normal" 
                            /\ sensorStates' = [sensorStates EXCEPT ![s] = "anomaly"] 
                            /\ Len(events) < MaxEvents
                            /\ events' = Append(events, "anomaly_detected:" \o ToString(s))
                            
Remove(seq, idx) == [j \in 1..(Len(seq)-1) |-> IF j < idx THEN seq[j] ELSE seq[j+1]]
  
FixAnomaly ==  \E i \in 1..Len(events), s \in Sensors:
                    /\ events[i] = "anomaly_detected:" \o ToString(s)
                    /\ sensorStates[s] = "anomaly"
                    /\ events' = Remove(events, i)
                    /\ sensorStates' = [sensorStates EXCEPT ![s] = "normal"]
   
(* Specification *)
Next == SensorReportAnomaly \/ FixAnomaly



Spec == /\ Init 
        /\ [][Next]_<<sensorStates, events>>

(* Properties *)
TypeOK == /\ sensorStates \in [Sensors -> {"normal", "anomaly"}]
          /\ events \in Seq(STRING)

(* Safety Properties *)
AnomalyAlwaysReportedInv == \A s \in Sensors:
                           sensorStates[s] = "anomaly" 
                           => \E i \in 1..Len(events): 
                                   events[i] = "anomaly_detected:" \o ToString(s)
AnomalyAlwaysReported == \A s \in Sensors:
                           sensorStates[s] = "anomaly" 
                           => []\E i \in 1..Len(events): 
                                   events[i] = "anomaly_detected:" \o ToString(s)



=============================================================================
       (* /\ WF_<<sensorStates, events>>(SensorMeasureAnomaly)
        /\ WF_<<sensorStates, events>>(SensorReportAnomaly)
        /\ WF_<<sensorStates, events>>(ControllerProcessAnomaly) \/ FixAnomaly*)         