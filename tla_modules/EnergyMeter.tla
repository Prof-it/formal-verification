-------------------------------- MODULE EnergyMeter --------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Meters
VARIABLES meterStates, events, alerts, billingStates, currentTime

(*--algorithm EnergyMeter
variables
  meterStates = [m \in Meters |-> "normal"],
  events = << >>,
  alerts = {},
  billingStates = [m \in Meters |-> "active"],
  currentTime = 0;

begin
  DetectAnomaly:
    either \E m \in Meters:
      meterStates[m] = "anomaly" ->
        events' := Append(events, "anomaly_detected"),
        alerts' := alerts \cup {currentTime},
        meterStates' := meterStates,
        billingStates' := billingStates,
        currentTime' := currentTime + 1;

  HandleAnomaly:
    either \E m \in Meters:
      meterStates[m] = "anomaly" ->
        meterStates' := meterStates,
        billingStates' := [billingStates EXCEPT ![m] = "paused"],
        events' := events,
        alerts' := alerts,
        currentTime' := currentTime;

end algorithm; *)

Init == 
  /\ meterStates = [m \in Meters |-> "unknown"]
  /\ events = << >>
  /\ alerts = {}
  /\ billingStates = [m \in Meters |-> "active"]
  /\ currentTime = 0

MeasureMeters ==
  \E m \in Meters:
    /\ meterStates[m] = "unknown" 
    /\ meterStates' = [meterStates EXCEPT ![m] = CHOOSE x \in {"normal", "anomaly"} : TRUE] 
    /\ currentTime' = currentTime + 1 
    /\ UNCHANGED <<events, alerts, billingStates>>

DetectAnomaly ==
  \E m \in Meters:
    /\ meterStates[m] = "anomaly" 
    /\ events' = Append(events, "anomaly_detected") 
    /\ alerts' = alerts \cup {currentTime} 
    /\ currentTime' = currentTime + 1 
    /\ UNCHANGED <<meterStates, billingStates>>

HandleAnomaly ==
  \E m \in Meters:
    /\ meterStates[m] = "anomaly" 
    /\ billingStates' = [billingStates EXCEPT ![m] = "paused"] 
    /\ currentTime' = currentTime 
    /\ UNCHANGED <<meterStates, events, alerts>>

Next == DetectAnomaly \/ HandleAnomaly

Spec == Init \/ [][Next]_<<meterStates, events, alerts, billingStates, currentTime>>

(* Properties *)
TypeOK == 
  meterStates \in [Meters -> {"normal", "anomaly", "unknown"}] /\
  billingStates \in [Meters -> {"active", "paused"}] /\
  events \in Seq(STRING) /\
  alerts \in SUBSET Nat /\
  currentTime \in Nat

NoBillingWhenAnomaly ==
  \A m \in Meters:
    meterStates[m] = "anomaly" => billingStates[m] = "paused"

AnomalyDetectedImpliesAlert ==
  \A m \in Meters:
    meterStates[m] = "anomaly" => alerts /= {}

MeterMeasurementInvariant ==
  \A m \in Meters:
    meterStates[m] = "unknown" => billingStates[m] = "active"

=============================================================================