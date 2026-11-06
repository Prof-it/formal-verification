------------------------- MODULE AgentActionBoundary -------------------------
\* SPDX-License-Identifier: Apache-2.0
\* Copyright (c) 2026 Dr. Tianxiang Lu
(***************************************************************************)
(* A minimal, implementation-neutral model of an execution boundary that   *)
(* writes an evidence log. It only shows that the rules in AgentActionRules *)
(* can be model-checked. FailOpen = TRUE models a common fault: a check    *)
(* that times out lets the action through as if it had passed.             *)
(***************************************************************************)
EXTENDS AgentActionRules

CONSTANTS Acts, MaxTime, FailOpen

VARIABLES log, now, phase, invalid, assured
vars == <<log, now, phase, invalid, assured>>

Pending == {"proposed", "authorized", "recorded"}

Ev(t, a, b, s) == [type |-> t, act |-> a, auth |-> a, key |-> a,
                   bound |-> b, assured |-> s, time |-> now]
Emit(t, a) == log' = Append(log, Ev(t, a, TRUE, assured))

Init == /\ log = << >>
        /\ now = 0
        /\ phase = [a \in Acts |-> "idle"]
        /\ invalid = [a \in Acts |-> FALSE]
        /\ assured = TRUE

Move(a, from, to) == phase[a] = from /\ phase' = [phase EXCEPT ![a] = to]

Propose(a)   == Move(a, "idle", "proposed") /\ Emit("propose", a)
                /\ UNCHANGED <<now, invalid, assured>>
Authorize(a) == assured /\ Move(a, "proposed", "authorized") /\ Emit("authorize", a)
                /\ UNCHANGED <<now, invalid, assured>>
Record(a)    == Move(a, "authorized", "recorded") /\ Emit("record", a)
                /\ UNCHANGED <<now, invalid, assured>>
Effect(a)    == /\ ~invalid[a]
                /\ assured \/ FailOpen
                /\ Move(a, "recorded", "effected")
                /\ Emit("effect", a)
                /\ UNCHANGED <<now, invalid, assured>>
Revoke(a)    == /\ phase[a] \in {"authorized", "recorded"} /\ ~invalid[a]
                /\ invalid' = [invalid EXCEPT ![a] = TRUE]
                /\ Emit("revoke", a)
                /\ UNCHANGED <<now, phase, assured>>
Dispose(a)   == /\ phase[a] \in Pending
                /\ phase' = [phase EXCEPT ![a] = "closed"]
                /\ Emit("dispose", a)
                /\ UNCHANGED <<now, invalid, assured>>
Verify(a)    == Move(a, "effected", "closed") /\ Emit("verify", a)
                /\ UNCHANGED <<now, invalid, assured>>
ChecksDown   == assured /\ assured' = FALSE /\ UNCHANGED <<log, now, phase, invalid>>
ChecksUp     == ~assured /\ assured' = TRUE /\ UNCHANGED <<log, now, phase, invalid>>

\* Timing assumption of this design: time does not pass a deadline while a
\* request or an effect is still open (the boundary decides in time).
Open(i) == \/ log[i].type = "propose"
              /\ phase[log[i].act] \in Pending
           \/ log[i].type = "effect"
              /\ phase[log[i].act] = "effected"
Tick == /\ now < MaxTime
        /\ \A i \in DOMAIN log : Open(i) => now + 1 <= log[i].time + T
        /\ now' = now + 1
        /\ UNCHANGED <<log, phase, invalid, assured>>

Next == \/ \E a \in Acts : Propose(a) \/ Authorize(a) \/ Record(a)
                           \/ Effect(a) \/ Revoke(a) \/ Dispose(a) \/ Verify(a)
        \/ ChecksDown \/ ChecksUp \/ Tick

Spec == Init /\ [][Next]_vars

\* The seven rules, checked in every reachable state.
RulesHold == AllRules(log, now)
=============================================================================
