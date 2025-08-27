---------------------------- MODULE MC_GDPR_Time ----------------------------
EXTENDS GDPR_Time, TLC

\* Define finite sets for data subjects and data types.
MC_DataSubjects == {"erni", "lisa", "bert"}
MC_Data == {"healthdata", "emaildata", "salarydata", "traveldata"}
MC_MAX_TIME == [year |-> 2500, month |-> 12, day |-> 31, hour |-> 23, minute |-> 59]


\* The set of initial events that the system will process.
\* All legal bases are now created by events.
MC_InitialEvents ==
    {
        \* Corresponds to legalObligation(erni, healthmanagement)
        [type |-> "StartContract",
         time |-> [year|->2025, month|->1, day|->1, hour|->0, minute|->0],
         subject |-> "erni",
         data |-> "healthdata",
         end_time |-> MC_MAX_TIME],
        
        \* Corresponds to contract(lisa, travelmanagement, 2501010800, 2791910800)
        [type |-> "StartContract",
         time |-> [year|->2501, month|->1, day|->1, hour|->8, minute|->0],
         subject |-> "lisa",
         data |-> "traveldata",
         end_time |-> MC_MAX_TIME],

        \* Corresponds to consent(erni, newslettermanagement, 2507120820)
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->20],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        
        \* Corresponds to a process start
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->25],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],

        \* Corresponds to consentWithdrawn(erni, newslettermanagement, 2507231035)
        [type |-> "WithdrawConsent",
         time |-> [year|->2025, month|->7, day|->23, hour|->10, minute|->35],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME]
    }
    
MC_Init ==
    /\ currentTime = MinTime(InitialEvents)
    /\ eventsToProcess = InitialEvents
    /\ activeProcesses = {}
    /\ activeLegalBases = {}
    /\ breachesInProgress = {}



=============================================================================
\* Modification History
\* Last modified Wed Aug 27 23:42:57 CEST 2025 by tianxiang.lu
\* Created Mon Aug 11 01:12:30 CEST 2025 by tianxiang.lu
