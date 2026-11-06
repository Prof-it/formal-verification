----------------------------- MODULE AgentActionRules -----------------------------
\* SPDX-License-Identifier: Apache-2.0
\* Copyright (c) 2026 Dr. Tianxiang Lu
(***************************************************************************)
(* Formal reading of seven rules for externally effective agent actions.            *)
(* Each rule is a predicate over an evidence log: a sequence of event      *)
(* records, as an evaluator would receive them. A rule can therefore be    *)
(* checked against a recorded log (trace checking) or, via a model that    *)
(* produces such logs, by the TLC model checker.                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT T        \* declared deadline for R1 and R2 (same unit as `time`)

EventTypes == {"propose", "authorize", "revoke", "expire", "trigger",
               "record", "effect", "dispose", "verify"}
Invalidating == {"revoke", "expire", "trigger"}

(* An event record. For "effect" events, `bound` and `assured` are the     *)
(* observed answers to: does the effect match its approval, and were the   *)
(* required checks in place? `key` is the uniqueness key (see 2.7).        *)
Event(Acts, Auths, Keys, MaxTime) ==
    [type : EventTypes, act : Acts, auth : Auths, key : Keys,
     bound : BOOLEAN, assured : BOOLEAN, time : 0..MaxTime]

Is(L, i, t) == L[i].type = t
Before(i) == 1..(i - 1)

-----------------------------------------------------------------------------
(* Type A: always rules *)

\* P1 Binding: whenever an action takes effect, it matches its approval.
P1(L) == \A i \in DOMAIN L : Is(L, i, "effect") => L[i].bound

\* P3 No duplicates: the same protected effect never occurs twice.
P3(L) == \A i, j \in DOMAIN L :
            (i < j /\ Is(L, i, "effect") /\ Is(L, j, "effect"))
                => L[i].key # L[j].key

\* P5 Checks in place: whenever an action takes effect, checks are in place.
P5(L) == \A i \in DOMAIN L : Is(L, i, "effect") => L[i].assured

(* Type B: order rules *)

\* P2 Validity: no effect before its approval, none after the approval is
\* revoked, expired or re-opened by a trigger.
P2(L) == \A i \in DOMAIN L : Is(L, i, "effect") =>
            /\ \E j \in Before(i) : Is(L, j, "authorize")
                                    /\ L[j].auth = L[i].auth
                                    /\ L[j].act = L[i].act
            /\ ~ \E j \in Before(i) : L[j].type \in Invalidating
                                      /\ L[j].auth = L[i].auth

\* P4 Record first: no effect before its decision record is committed.
P4(L) == \A i \in DOMAIN L : Is(L, i, "effect") =>
            \E j \in Before(i) : Is(L, j, "record") /\ L[j].act = L[i].act

(* Type C: deadline rules. `now` is the time the log is evaluated; a       *)
(* request still inside its deadline is not (yet) a breach.                *)

\* R1 Every request gets an outcome within T.
R1(L, now) == \A i \in DOMAIN L : Is(L, i, "propose") =>
            \/ \E j \in DOMAIN L : /\ j > i
                                   /\ L[j].type \in {"effect", "dispose"}
                                   /\ L[j].act = L[i].act
                                   /\ L[j].time <= L[i].time + T
            \/ now <= L[i].time + T

\* R2 Effects are checked within T.
R2(L, now) == \A i \in DOMAIN L : Is(L, i, "effect") =>
            \/ \E j \in DOMAIN L : /\ j > i
                                   /\ Is(L, j, "verify")
                                   /\ L[j].act = L[i].act
                                   /\ L[j].time <= L[i].time + T
            \/ now <= L[i].time + T

AllRules(L, now) == P1(L) /\ P2(L) /\ P3(L) /\ P4(L) /\ P5(L)
                    /\ R1(L, now) /\ R2(L, now)
=============================================================================
