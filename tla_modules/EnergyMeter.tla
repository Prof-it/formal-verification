-------------------------------- MODULE EnergyMeter --------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Sensors, Controllers
VARIABLES sensorStates, events

Init == 
  /\ sensorStates = [s \in Sensors |-> "unknown"]
  /\ events = << >>

SensorMeasureNormal ==
  \E s \in Sensors:
    /\ sensorStates' = [sensorStates EXCEPT ![s] = "normal"]
    /\ UNCHANGED <<events>>

SensorMeasureAnomaly ==
  \E s \in Sensors:
    /\ sensorStates' = [sensorStates EXCEPT ![s] = "anomaly"]
    /\ UNCHANGED <<events>>


SensorReportAnomaly ==
  \E s \in Sensors:
    /\ sensorStates[s] = "anomaly" 
    /\ events' = Append(events, "anomaly_detected: " \o s)
    /\ UNCHANGED <<sensorStates>>

ControllerProcessAnomaly == 
  \E c \in Controllers:
    /\ events /= << >>
    /\ events' = << >>
    /\ UNCHANGED <<sensorStates>>

Next == 
  \/ SensorMeasureNormal
  \/ SensorMeasureAnomaly
  \/ SensorReportAnomaly
  \/ ControllerProcessAnomaly

Spec == Init /\ [][Next]_<<sensorStates, events>>
          /\ WF_<<sensorStates, events>>(SensorMeasureNormal)
          /\ WF_<<sensorStates, events>>(SensorMeasureAnomaly)
          /\ WF_<<sensorStates, events>>(SensorReportAnomaly)
          /\ WF_<<sensorStates, events>>(ControllerProcessAnomaly)
(* Properties *)
TypeOK == 
  sensorStates \in [Sensors -> {"normal", "anomaly", "unknown"}] /\
  events \in Seq(STRING)

(* Safety Properties *)
AnomalyAlwaysReported ==
  \A s \in Sensors:
    sensorStates[s] = "anomaly" => []\E i \in 1..Len(events):
      events[i] = "anomaly_detected " \o s

(* Liveness Properties *)
MeasurementsEventuallyHappen ==
  \A s \in Sensors:
    sensorStates[s] = "unknown" => <>(sensorStates[s] \in {"normal", "anomaly"})

=============================================================================