EXTENDS Integers, Sequences, TLC

CONSTANTS Meters
VARIABLES meterStates, events, alerts, billingStates

(*--algorithm EnergyMeter
variables
  meterStates = [m \in Meters |-> "normal"],
  events = << >>,
  alerts = {},
  billingStates = [m \in Meters |-> "active"];

begin
  DetectAnomaly:
    either \E m \in Meters:
      meterStates[m] = "anomaly" ->
        events' := Append(events, "anomaly_detected"),
        alerts' := alerts \cup {CurrentTimestamp},
        meterStates' := meterStates,
        billingStates' := billingStates;

  HandleAnomaly:
    either \E m \in Meters:
      meterStates[m] = "anomaly" ->
        meterStates' := meterStates,
        billingStates' := [billingStates EXCEPT ![m] = "paused"],
        events' := events,
        alerts' := alerts;

end algorithm; *)

Init == 
  /\ meterStates = [m \in Meters |-> "normal"]
  /\ events = << >>
  /\ alerts = {}
  /\ billingStates = [m \in Meters |-> "active"]

DetectAnomaly ==
  \E m \in Meters:
    meterStates[m] = "anomaly" /\
    events' = Append(events, "anomaly_detected") /\
    alerts' = alerts \cup {CurrentTimestamp} /\
    meterStates' = meterStates /\
    billingStates' = billingStates

HandleAnomaly ==
  \E m \in Meters:
    meterStates[m] = "anomaly" /\
    meterStates' = meterStates /\
    billingStates' = [billingStates EXCEPT ![m] = "paused"] /\
    events' = events /\
    alerts' = alerts

Next == DetectAnomaly \/ HandleAnomaly

Spec == Init \/ [][Next]_<<meterStates, events, alerts, billingStates>>

(* Properties *)
TypeOK == 
  meterStates \in [Meters -> {"normal", "anomaly"}] /\
  billingStates \in [Meters -> {"active", "paused"}] /\
  events \in Seq(String) /\
  alerts \in SetOf(Nat)

NoBillingWhenAnomaly ==
  \A m \in Meters:
    meterStates[m] = "anomaly" => billingStates[m] = "paused"

AnomalyDetectedImpliesAlert ==
  \A m \in Meters:
    meterStates[m] = "anomaly" => alerts /= {}
