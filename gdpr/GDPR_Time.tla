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
    breachesInProgress


InitialTime == IF InitialEvents = {} THEN
                  [year |-> FixedEpochYear, month |-> 1, day |-> 1, hour |-> 0, minute |-> 0]
               ELSE MinTime(InitialEvents)

EndTime == IF InitialEvents = {} THEN
                [year |-> FixedEpochYear + 50, month |-> 12, day |-> 31, 
                                               hour |-> 23, minute |-> 59]
           ELSE MaxTime(InitialEvents)



Init == /\ currentTime = InitialTime
        /\ eventsToProcess = InitialEvents
        /\ activeProcesses = {}
        /\ activeLegalBases = {}
        /\ breachesInProgress = {}

StartProcessing(e) ==
    /\ e.type = "StartProcessing"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeProcesses' = activeProcesses \cup {[subject |-> e.subject,
                                                    data |-> e.data,
                                                    start|-> e.time,
                                                     end |-> EndTime ]}
    /\ UNCHANGED <<activeLegalBases, breachesInProgress>>

GiveConsent(e) ==
    /\ e.type = "GiveConsent"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeLegalBases' = activeLegalBases \cup {[type |-> "Consent",
                                                subject |-> e.subject,
                                                data    |-> e.data,
                                                start   |-> e.time,
                                                end     |-> EndTime]}
    /\ UNCHANGED <<activeProcesses, breachesInProgress>>

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
            /\ UNCHANGED <<activeProcesses, breachesInProgress>>


StartContract(e) ==
    /\ e.type = "StartContract"
    /\ eventsToProcess' = eventsToProcess \ {e}
    /\ currentTime' = e.time
    /\ activeLegalBases' = activeLegalBases \cup {[ type |-> "Contract",
                                                 subject |-> e.subject,
                                                    data |-> e.data,
                                                   start |-> e.time,
                                                     end |-> e.end_time]}
    /\ UNCHANGED <<activeProcesses, breachesInProgress>>

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
        /\ UNCHANGED <<activeProcesses, breachesInProgress>>
        
HasLegalBasis(p) ==
    \E l \in activeLegalBases:
        /\ p.subject = l.subject
        /\ p.data = l.data
        /\ TimeBetween(l.start, l.end, currentTime)
        

BreachOccurs ==
        \E p \in activeProcesses: 
            /\ ~HasLegalBasis(p) 
            /\ [process |-> p, status |-> "Pending"] \notin breachesInProgress
            /\ breachesInProgress' = breachesInProgress 
                                   \cup {[ process |-> p,
                                            status |-> "Pending",
                                        breachTime |-> currentTime
                                         ]
                                        }
            /\ UNCHANGED <<currentTime, activeProcesses, activeLegalBases, eventsToProcess>>

ReportBreach ==
    \E b \in breachesInProgress:
        /\ b.status = "Pending"
        /\ breachesInProgress' = (breachesInProgress \ {b}) \cup {[b EXCEPT !.status = "Reported"]}
        /\ UNCHANGED <<currentTime, activeProcesses, activeLegalBases, eventsToProcess>>
Next ==
    \* Event-driven actions
    \/ \E e \in eventsToProcess:
       /\ e.time = MinTime(eventsToProcess)
       /\\/ GiveConsent(e)
         \/ WithdrawConsent(e)
         \/ StartProcessing(e)
         \/ StartContract(e)
         \/ EndContract(e)
    \* State-driven actions
    \/ BreachOccurs
    \/ ReportBreach

vars == <<activeProcesses, activeLegalBases, breachesInProgress, eventsToProcess, currentTime>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================