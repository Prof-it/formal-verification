-------------------------------- MODULE EnergyMeter --------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Sensors, Controllers, MaxEvents
VARIABLES sensorStates, events

Init == 
  /\ sensorStates = [s \in Sensors |-> "normal"]
  /\ events = << >>


SensorMeasureAnomaly ==
  \E s \in Sensors:
    /\ sensorStates[s] # "anomaly"
    /\ sensorStates' = [sensorStates EXCEPT ![s] = "anomaly"]
    /\ UNCHANGED <<events>>


SensorReportAnomaly ==
  \E s \in Sensors:
    /\ sensorStates[s] = "anomaly" 
    /\ Len(events) < MaxEvents
    /\ events' = Append(events, "anomaly_detected: " \o s)
    /\ UNCHANGED <<sensorStates>>

ControllerProcessAnomaly == 
  \E c \in Controllers:
    /\ events /= << >>
    /\ events' = << >>
    /\ UNCHANGED <<sensorStates>>

Next == 
  \/ SensorMeasureAnomaly
  \/ SensorReportAnomaly
  \/ ControllerProcessAnomaly

Spec == Init 
        /\ [][Next]_<<sensorStates, events>>
(* Properties *)
TypeOK == 
  sensorStates \in [Sensors -> {"normal", "anomaly"}] /\
  events \in Seq(STRING)

(* Safety Properties *)
AnomalyAlwaysReported ==
  \A s \in Sensors:
    sensorStates[s] = "anomaly" => []\E i \in 1..Len(events):
      events[i] = "anomaly_detected " \o s



=============================================================================