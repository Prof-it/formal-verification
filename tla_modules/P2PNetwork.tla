EXTENDS Integers, Sequences, TLC, EnergyMeter

CONSTANTS Nodes, AuthorityNode
VARIABLES messages, routes, alerts

(*--algorithm P2PNetwork
variables
  messages = << >>,
  routes = {},
  alerts = {};

begin
  SendAlert:
    either \E meter \in Nodes:
      meter.type = "meter" /\ meter.state = "anomaly" ->
        messages' := Append(messages, [src |-> meter.id, dest |-> AuthorityNode, type |-> "alert"]),
        routes' := routes,
        alerts' := alerts;

  RouteMessage:
    either \E msg \in messages:
      \E n \in Nodes:
        RoutingTable(n, msg.dest) = NextHop ->
          messages' := (messages \ {msg}) \cup {msg \ {src |-> NextHop}},
          routes' := routes \cup {[msg |-> NextHop]},
          alerts' := alerts;

  Deliver:
    either \E msg \in messages:
      msg.dest = LocalNode ->
        alerts' := alerts \cup {msg},
        messages' := messages \ {msg},
        routes' := routes;

end algorithm; *)

Init == 
  messages = << >> /\
  routes = {} /\
  alerts = {}

SendAlert ==
  \E meter \in Nodes:
    meter.type = "meter" /\ meter.state = "anomaly" /\
    messages' = Append(messages, [src |-> meter.id, dest |-> AuthorityNode, type |-> "alert"]) /\
    routes' = routes /\
    alerts' = alerts

RouteMessage ==
  \E msg \in messages:
    \E n \in Nodes:
      RoutingTable(n, msg.dest) = NextHop /\
      messages' = (messages \ {msg}) \cup {msg \ {src |-> NextHop}} /\
      routes' = routes \cup {[msg |-> NextHop]} /\
      alerts' = alerts

Deliver ==
  \E msg \in messages:
    msg.dest = LocalNode /\
    alerts' = alerts \cup {msg} /\
    messages' = messages \ {msg} /\
    routes' = routes

Next == SendAlert \/ RouteMessage \/ Deliver

Spec == Init \/ [][Next]_<<messages, routes, alerts>>

(* Properties *)
TypeOK == 
  messages \in Seq([src: Nodes, dest: Nodes, type: String]) /\
  routes \in [messages -> Nodes] /\
  alerts \in SetOf([src: Nodes, dest: Nodes, type: String])

MessageDeliveryInvariant ==
  \A msg \in DOMAIN routes:
    \E n \in Nodes:
      n = msg.src /\ msg.dest = AuthorityNode

NoDuplicateMessages ==
  \A msg1, msg2 \in messages:
    msg1 /= msg2 => msg1.src /= msg2.src \/ msg1.dest /= msg2.dest
