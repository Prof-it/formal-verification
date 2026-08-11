---------------------------- MODULE GDPR_Time ----------------------------
EXTENDS Naturals, TimeUtils, Sequences

CONSTANTS
    DataSubjects,
    Data,
    InitialEvents
    
TimePoint == { e.time : e \in InitialEvents } \cup { e.end_time : e \in InitialEvents }

EventRecordTypes == {"StartProcessing", "GiveConsent", "WithdrawConsent", 
                             "StartContract", "EndContract"}

Event == [type: EventRecordTypes, time: TimePoint, subject: DataSubjects, 
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


VARIABLES
    currentTime,
    eventsToProcess,
    activeProcesses,
    activeLegalBases,
    incidentsInProgress

vars == <<activeProcesses, activeLegalBases, incidentsInProgress, eventsToProcess, currentTime>>

InitialTime == IF InitialEvents = {} THEN
                   [year |-> Min({FixedEpochYear} \cup YearRange), month |-> 1, day |-> 1, hour |-> 0, minute |-> 0]
                ELSE MinTime(InitialEvents)

EndTime == IF InitialEvents = {} THEN
                [year |-> Max({FixedEpochYear} \cup YearRange), month |-> 12, day |-> 31, 
                                               hour |-> 23, minute |-> 59]
           ELSE MaxTime(InitialEvents)



Init == /\ currentTime = InitialTime
        /\ eventsToProcess = InitialEvents
        /\ activeProcesses = {}
        /\ activeLegalBases = {}
        /\ incidentsInProgress = {}

StartProcessing(e) ==
    /\ e.type = "StartProcessing"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeProcesses' = activeProcesses \cup {[subject |-> e.subject,
                                                    data |-> e.data,
                                                    start|-> e.time,
                                                     end |-> EndTime ]}
    /\ UNCHANGED <<activeLegalBases, incidentsInProgress>>

GiveConsent(e) ==
    /\ e.type = "GiveConsent"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeLegalBases' = activeLegalBases \cup {[type |-> "Consent",
                                                subject |-> e.subject,
                                                data    |-> e.data,
                                                start   |-> e.time,
                                                end     |-> EndTime]}
    /\ UNCHANGED <<activeProcesses, incidentsInProgress>>

WithdrawConsent(e) ==
        /\ e.type = "WithdrawConsent"
        /\ \E c \in activeLegalBases: 
            c.type = "Consent" /\ c.subject = e.subject /\ c.data = e.data
        /\ LET consentToRemove == CHOOSE c \in activeLegalBases:
                              c.type = "Consent" /\ c.subject = e.subject /\ c.data = e.data
           IN
            /\ eventsToProcess' = eventsToProcess \ {e}
            /\ currentTime' = e.time
            /\ activeLegalBases' = (activeLegalBases \ {consentToRemove}) 
                                    \cup {[ type    |-> consentToRemove.type,
                                            subject |-> consentToRemove.subject,
                                            data    |-> consentToRemove.data,
                                            start   |-> consentToRemove.start,
                                            end     |-> e.time ]}
            /\ UNCHANGED <<activeProcesses, incidentsInProgress>>


StartContract(e) ==
    /\ e.type = "StartContract"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeLegalBases' = activeLegalBases \cup {[ type |-> "Contract",
                                                 subject |-> e.subject,
                                                    data |-> e.data,
                                                   start |-> e.time,
                                                     end |-> e.end_time]}
    /\ UNCHANGED <<activeProcesses, incidentsInProgress>>

EndContract(e) ==
    /\ e.type = "EndContract"
    /\ \E c \in activeLegalBases: 
       c.type = "Contract" /\ c.subject = e.subject /\ c.data = e.data
    /\ LET contractToEnd == CHOOSE c \in activeLegalBases:
                               c.type = "Contract" /\ c.subject = e.subject /\ c.data = e.data
       IN
        /\ contractToEnd \in activeLegalBases
        /\ eventsToProcess' = eventsToProcess \ {e}
        /\ currentTime' = e.time
        /\ activeLegalBases' = (activeLegalBases \ {contractToEnd}) 
                                \cup {[ type    |-> contractToEnd.type,
                                        subject |-> contractToEnd.subject,
                                        data    |-> contractToEnd.data,
                                        start   |-> contractToEnd.start,
                                        end     |-> e.time ]}
        /\ UNCHANGED <<activeProcesses, incidentsInProgress>>
        
HasLegalBasis(p) ==
    \E l \in activeLegalBases:
        /\ p.subject = l.subject
        /\ p.data = l.data
        /\ TimeBetween(l.start, l.end, currentTime)
        


ComplianceIncident ==
        \E p \in activeProcesses: 
            /\ ~HasLegalBasis(p) 
            /\ [process |-> p, status |-> "Pending"] \notin incidentsInProgress
            /\ incidentsInProgress' = incidentsInProgress 
                                   \cup {[ process |-> p,
                                            status |-> "Pending",
                                        incidentTime |-> currentTime
                                         ]
                                        }
            /\ UNCHANGED <<currentTime, activeProcesses, activeLegalBases, eventsToProcess>>

ReportIncident ==
    \E b \in incidentsInProgress:
        /\ b.status = "Pending"
        /\ incidentsInProgress' = (incidentsInProgress \ {b}) \cup {[b EXCEPT !.status = "Reported"]}
        /\ UNCHANGED <<currentTime, activeProcesses, activeLegalBases, eventsToProcess>>

\* TerminateProcess action: removes processes whose end time has passed or legal basis is no longer valid
TerminateProcess ==
    \E p \in activeProcesses:
        ( ~HasLegalBasis(p)
          \/ LinearTime(currentTime) >= LinearTime(p.end)
        )
        /\ activeProcesses' = activeProcesses \ {p}
        /\ UNCHANGED <<currentTime, activeLegalBases, incidentsInProgress, eventsToProcess>>
\* Advances currentTime to the next event's time if no other actions are enabled
TimeAdvance ==
    /\ eventsToProcess # {}
    /\ LET t == MinTime(eventsToProcess)
       IN /\ LinearTime(currentTime) < LinearTime(t)
          /\ currentTime' = t
    /\ UNCHANGED <<activeProcesses, activeLegalBases, incidentsInProgress, eventsToProcess>>
\* Removes events that are scheduled after the maximum allowed time
RemoveUnreachableEvents ==
    \E e \in eventsToProcess:
        LinearTime(e.time) > LinearTime(FixedEndTime) /\
        eventsToProcess' = eventsToProcess \ {e} /\
        UNCHANGED <<currentTime, activeProcesses, activeLegalBases, incidentsInProgress>>

Next ==
    \* Event-driven actions
    \/ (\E e \in eventsToProcess:
            /\ e.time = MinTime(eventsToProcess)
            /\ (GiveConsent(e)
                \/ WithdrawConsent(e)
                \/ StartProcessing(e)
                \/ StartContract(e)
                \/ EndContract(e))
        )
    \* State-driven actions
    \/ ComplianceIncident
    \/ ReportIncident
    \/ TerminateProcess
    \/ RemoveUnreachableEvents
    \/ TimeAdvance
    \/ UNCHANGED vars


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------
TypeInvariant ==
    /\ currentTime \in TimePoint
    /\ eventsToProcess \subseteq InitialEvents
    /\ activeProcesses \subseteq Process
    /\ activeLegalBases \subseteq LegalBasis


=============================================================================
