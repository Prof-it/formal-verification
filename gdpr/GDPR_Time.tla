---------------------------- MODULE GDPR_Time ----------------------------
EXTENDS Naturals, TimeUtils, Sequences

CONSTANTS
    DataSubjects,
    Data,
    InitialEvents


\* Extend EventTypes for DataBreachDetected
EventTypes == {"StartProcessing", "GiveConsent", "WithdrawConsent", 
                               "StartContract", "EndContract", "DataBreachDetected", "DataBreachReported"}



TimePoint == { e.time : e \in InitialEvents } \cup { e.end_time : e \in InitialEvents }

Event == [type: EventTypes, time: TimePoint, subject: DataSubjects, 
                                   data: Data, end_time: TimePoint]

LegalBasis == [ type: {"Consent", "Contract"},
                subject: DataSubjects,
                data: Data,
                start: TimePoint,
                end: TimePoint ]

Process ==[ subject: DataSubjects,
            data: Data,
            start: TimePoint,
            end: TimePoint ]

\* DataBreach: minimal, only type and time (DPV-aligned)
DataBreach == [event: Event, status: {"Pending", "Reported"}]
Incident == [process: Process, status: {"Pending", "Recorded"}, incidentTime: TimePoint]

VARIABLES
    now,
    events,
    processes,
    legalBases,
    incidents,
    breaches

vars == <<now, events, processes, legalBases, incidents, breaches>>

InitialTime == IF InitialEvents = {} THEN
                   [year |-> Min({FixedEpochYear} \cup YearRange), month |-> 1, day |-> 1, hour |-> 0, minute |-> 0]
                ELSE MinTime(InitialEvents)

EndTime == IF InitialEvents = {} THEN
                [year |-> Max({FixedEpochYear} \cup YearRange), month |-> 12, day |-> 31, 
                                               hour |-> 23, minute |-> 59]
           ELSE MaxTime(InitialEvents)



Init == /\ now = InitialTime
        /\ events = InitialEvents
        /\ processes = {}
        /\ legalBases = {}
        /\ incidents = {}
        /\ breaches = {}

StartProcessing(e) ==
    /\ e.type = "StartProcessing"
    /\ events' = events \ {e}
    /\ now' = e.time
    /\ processes' = processes \cup {[subject |-> e.subject,
                                                    data |-> e.data,
                                                    start|-> e.time,
                                                     end |-> EndTime ]}
    /\ UNCHANGED <<legalBases, incidents, breaches>>

GiveConsent(e) ==
    /\ e.type = "GiveConsent"
    /\ events' = events \ {e}
    /\ now' = e.time
    /\ legalBases' = legalBases \cup {[type |-> "Consent",
                                                subject |-> e.subject,
                                                data    |-> e.data,
                                                start   |-> e.time,
                                                end     |-> EndTime]}
    /\ UNCHANGED <<processes, incidents, breaches>>

WithdrawConsent(e) ==
        /\ e.type = "WithdrawConsent"
        /\ \E c \in legalBases: 
            c.type = "Consent" /\ c.subject = e.subject /\ c.data = e.data
        /\ LET consentToRemove == CHOOSE c \in legalBases:
                              c.type = "Consent" /\ c.subject = e.subject /\ c.data = e.data
           IN
            /\ events' = events \ {e}
            /\ now' = e.time
            /\ legalBases' = (legalBases \ {consentToRemove}) 
                                    \cup {[ type    |-> consentToRemove.type,
                                            subject |-> consentToRemove.subject,
                                            data    |-> consentToRemove.data,
                                            start   |-> consentToRemove.start,
                                            end     |-> e.time ]}
            /\ UNCHANGED <<processes, incidents, breaches>>

\* Action: Detect a data breach event (e.g., by hash/integrity/ransomware evidence)
DetectDataBreach(e) ==
    /\ e.type = "DataBreachDetected"
    /\ events' = events \ {e}
    /\ now' = e.time
    /\ breaches' = breaches 
                                 \cup {[ event |-> e,
                                        status |-> "Pending"]}    
    /\ UNCHANGED <<processes, legalBases, incidents>>

BreachMatchBySubjectData(e) ==
    {b \in breaches : 
        b.event.subject = e.subject /\ b.event.data = e.data}

DataBreachReported(e) ==
    /\ e.type = "DataBreachReported"
    /\ \E b \in BreachMatchBySubjectData(e):
        b.status = "Pending"
    /\ LET breachToReport == CHOOSE b \in BreachMatchBySubjectData(e):
                              b.status = "Pending"
       IN
        /\ events' = events \ {e}
        /\ now' = e.time
        /\ breaches' = (breaches \ {breachToReport}) 
                                     \cup {[ breachToReport EXCEPT !.status = "Reported"]}
        /\ UNCHANGED <<processes, legalBases, incidents>>

StartContract(e) ==
    /\ e.type = "StartContract"
    /\ events' = events \ {e}
    /\ now' = e.time
    /\ legalBases' = legalBases \cup {[ type |-> "Contract",
                                                 subject |-> e.subject,
                                                    data |-> e.data,
                                                   start |-> e.time,
                                                     end |-> e.end_time]}
    /\ UNCHANGED <<processes, incidents, breaches>>

EndContract(e) ==
    /\ e.type = "EndContract"
    /\ \E c \in legalBases: 
       c.type = "Contract" /\ c.subject = e.subject /\ c.data = e.data
    /\ LET contractToEnd == CHOOSE c \in legalBases:
                               c.type = "Contract" /\ c.subject = e.subject /\ c.data = e.data
       IN
        /\ contractToEnd \in legalBases
        /\ events' = events \ {e}
        /\ now' = e.time
        /\ legalBases' = (legalBases \ {contractToEnd}) 
                                \cup {[ type    |-> contractToEnd.type,
                                        subject |-> contractToEnd.subject,
                                        data    |-> contractToEnd.data,
                                        start   |-> contractToEnd.start,
                                        end     |-> e.time ]}
        /\ UNCHANGED <<processes, incidents, breaches>>
        
HasLegalBasis(p) ==
    \E l \in legalBases:
        /\ p.subject = l.subject
        /\ p.data = l.data
        /\ TimeBetween(l.start, l.end, now)
        


ComplianceIncident ==
        \E p \in processes: 
            /\ ~HasLegalBasis(p) 
            /\ [process |-> p, status |-> "Pending"] \notin incidents
            /\ incidents' = incidents 
                                   \cup {[ process |-> p,
                                            status |-> "Pending",
                                            incidentTime |-> now
                                         ]
                                        }
            /\ UNCHANGED <<now, processes, legalBases, events,breaches>>

RecordIncident ==
    \E i \in incidents:
        /\ i.status = "Pending"
        /\ incidents' = (incidents \ {i}) 
                                \cup {[i EXCEPT !.status = "Recorded"]}
        /\ UNCHANGED <<now, processes, legalBases, events, breaches>>


\* TerminateProcess action: removes processes whose end time has passed or legal basis is no longer valid
TerminateProcess ==
    \E p \in processes:
        ( ~HasLegalBasis(p)
          \/ ToMinutes(now) >= ToMinutes(p.end)
        )
        /\ processes' = processes \ {p}
        /\ UNCHANGED <<now, legalBases, incidents, breaches, events>>

\* Removes events that are scheduled after the maximum allowed time
RemoveUnreachableEvents ==
    \E e \in events:
        ToMinutes(e.time) > ToMinutes(FixedEndTime) /\
        events' = events \ {e} /\
        UNCHANGED <<now, processes, legalBases, incidents, breaches>>

\* Advances now to the next event's time if no other actions are enabled
TimeAdvance ==
    /\ events # {}
    /\ LET t == MinTime(events)
       IN /\ ToMinutes(now) < ToMinutes(t)
          /\ now' = t
    /\ UNCHANGED <<processes, legalBases, incidents, breaches, events>>


Next ==
    \* Event-driven actions
    \/ (\E e \in events:
            /\ e.time = MinTime(events)
            /\ (GiveConsent(e)
                \/ WithdrawConsent(e)
                \/ StartProcessing(e)
                \/ StartContract(e)
                \/ EndContract(e)
                \/ DetectDataBreach(e)
                \/ DataBreachReported(e))
        )
    \* State-driven actions
    \/ ComplianceIncident
    \/ RecordIncident
    \/ TerminateProcess
    \/ RemoveUnreachableEvents
    \/ TimeAdvance
    \/ UNCHANGED vars


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------
TypeInvariant ==
    /\ now \in TimePoint
    /\ events \subseteq InitialEvents
    /\ processes \subseteq Process
    /\ legalBases \subseteq LegalBasis
    /\ incidents \subseteq Incident
    /\ breaches \subseteq DataBreach


=============================================================================
