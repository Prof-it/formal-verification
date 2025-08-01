-------------------------------- MODULE P2PNetwork --------------------------------
EXTENDS Integers, Sequences, TLC, Naturals, FiniteSets

CONSTANTS ControllerNode, AuthorityNode, Payloads, MessageType
Nodes == {ControllerNode, AuthorityNode}
VARIABLES messages, alerts
RemoveElement(s, e) ==
    IF \E i \in 1..Len(s) : s[i] = e
    THEN
        LET index == CHOOSE i \in 1..Len(s) : s[i] = e
        IN SubSeq(s, 1, index - 1) \o SubSeq(s, index + 1, Len(s))
    ELSE s (* If element not found, return original sequence *)
    
    


(* Action *)
SendAlert(payload) == 
  LET newMsg == [src |-> ControllerNode, dest |-> AuthorityNode, type |-> "alert", data |-> payload]
  IN
    /\ ~(\E i \in 1..Len(messages): messages[i] = newMsg)
    /\ messages' = Append(messages, newMsg)
    /\ UNCHANGED alerts

Deliver ==
  \E i \in 1..Len(messages):
    /\ messages[i].dest = AuthorityNode
    /\ alerts' = alerts \cup {messages[i]}
    /\ messages' = RemoveElement(messages, messages[i])


Init == 
  /\ messages = << >>
  /\ alerts = {}
  
Next == \E payload \in Payloads: \/ SendAlert(payload)
                                 \/ Deliver

vars == <<messages, alerts>>
Spec == Init /\ [][Next]_vars

(* Invariants *)
NoDuplicateMessages ==
  \A i, j \in 1..Len(messages):
    i # j => messages[i] # messages[j]

TypeOK == 
  /\ messages \in Seq([src: Nodes, dest: Nodes, type: MessageType, data: Payloads]) 
  /\ alerts \subseteq [src: Nodes, dest: Nodes, type: MessageType, data: Payloads]

INVARIANTS == NoDuplicateMessages /\ TypeOK

=============================================================================
(* RouteMessage ==
  \E msg \in messages:
    \E n \in Nodes:
      /\ RoutingTable(n, msg.dest) = NextHop 
      /\ messages' = (messages \ {msg}) \cup {msg \ {src |-> NextHop}}
      /\ routes' = routes \cup {[msg |-> NextHop]}
      /\ alerts' = alerts *)

(* MessageDeliveryInvariant ==
  \A msg \in DOMAIN routes:
    \E n \in Nodes:
      n = msg.src /\ msg.dest = AuthorityNode *)
(* For TLC to explore, Next needs to allow SendAlert with some payload or Deliver *)
(* This will be refined when integrating with AnomalyAlertModel *)