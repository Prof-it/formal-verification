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
  /\ meterStates \in [Meters -> {"normal", "anomaly"}]
  /\ events = << >>
  /\ alerts = {}
  /\ billingStates = [m \in Meters |-> "active"]
  /\ currentTime = 0

DetectAnomaly ==
  \E m \in Meters:
    meterStates[m] = "anomaly" /\
    events' = Append(events, "anomaly_detected") /\
    alerts' = alerts \cup {currentTime} /\
    meterStates' = meterStates /\
    billingStates' = billingStates /\
    currentTime' = currentTime + 1

HandleAnomaly ==
  \E m \in Meters:
    meterStates[m] = "anomaly" /\
    meterStates' = meterStates /\
    billingStates' = [billingStates EXCEPT ![m] = "paused"] /\
    events' = events /\
    alerts' = alerts /\
    currentTime' = currentTime

Next == DetectAnomaly \/ HandleAnomaly

Spec == Init \/ [][Next]_<<meterStates, events, alerts, billingStates, currentTime>>

(* Properties *)
TypeOK == 
  meterStates \in [Meters -> {"normal", "anomaly"}] /\
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

=============================================================================