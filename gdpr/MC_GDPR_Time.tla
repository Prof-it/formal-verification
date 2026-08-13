---------------------------- MODULE MC_GDPR_Time ----------------------------
EXTENDS GDPR_Rules, TLC

\* Define finite sets for data subjects and data types.
MC_DataSubjects == {"erni", "lisa", "bert"}
MC_Data == {"healthdata", "emaildata", "salarydata", "traveldata"}
MC_MAX_TIME == [year |-> 2500, month |-> 12, day |-> 31, hour |-> 23, minute |-> 59]
MC_YearRange == {2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2050}
MC_MonthRange == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
MC_DayRange == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}
MC_HourRange == {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}
MC_MinuteRange == {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
                  50, 51, 52, 53, 54, 55, 56, 57, 58, 59}   

\* MC_TimePoints can be a subset of the full range if desired, or use the full range for enumeration
\* MC_TimePoints can be a subset of the full range if desired, or use the full range for enumeration
\* MC_TimePoints is not used; rely on TimePoints from TimeUtils.tla
\* The set of initial events that the system will process.
\* All legal bases are now created by events.

\* Dedicated initial event sets for each scenario
MC_InitialEventConsentWithdrawn ==
    {
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->20],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "WithdrawConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->30],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->35],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME]
    }

MC_InitialEventValidConsent ==
    {
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->20],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->25],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME]
    }

MC_InitialEventMissingConsent ==
    {
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->25],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME]
    }


MC_InitialEventDeadlineViolation ==
    {
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->20],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->25],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "DataBreachDetected",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->30],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME],
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->15, hour|->8, minute|->31],
         subject |-> "erni",
         data |-> "emaildata",
         end_time |-> MC_MAX_TIME]
    }

\* New scenario: Correct report breach (no deadline violation)
MC_InitialEventReportBreachNoViolation ==
    {
        [type |-> "GiveConsent",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->20],
         subject |-> "lisa",
         data |-> "salarydata",
         end_time |-> MC_MAX_TIME],
        [type |-> "StartProcessing",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->25],
         subject |-> "lisa",
         data |-> "salarydata",
         end_time |-> MC_MAX_TIME],
        [type |-> "DataBreachDetected",
         time |-> [year|->2025, month|->7, day|->12, hour|->8, minute|->30],
         subject |-> "lisa",
         data |-> "salarydata",
         end_time |-> MC_MAX_TIME],
        [type |-> "DataBreachReported",
         time |-> [year|->2025, month|->7, day|->12, hour|->9, minute|->0],
         subject |-> "lisa",
         data |-> "salarydata",
         end_time |-> MC_MAX_TIME]
    }

\* The original MC_InitialEvents is now deprecated and should not be used. Use MC_InitialEvent* constants instead.
    
MC_Init ==
    /\ now = MinTime(InitialEvents)
    /\ events = InitialEvents
    /\ processes = {}
    /\ legalBases = {}
    /\ incidents = {}



=============================================================================
\* Modification History
\* Last modified Mon Sep 08 22:07:40 CEST 2025 by tianxiang.lu
\* Created Mon Aug 11 01:12:30 CEST 2025 by tianxiang.lu
\* Explicit finite sets for time fields to help TLC enumerate records
