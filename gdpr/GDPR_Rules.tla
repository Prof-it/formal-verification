----------------------------- MODULE GDPR_Rules -----------------------------
EXTENDS GDPR_Time

---------------------------------

(*Rule 1: Legal Basis Requirement
  If personal data is being processed, there must be a legal basis for it.*)
AllProcessingIsLawful ==
    \A p \in activeProcesses:
        \E l \in activeLegalBases:
            /\ p.subject = l.subject
            /\ p.data = l.data
            /\ TimeBetween(l.start, l.end, currentTime)
(*Rule 2: Legal Basis Types
A legal basis must be a recognized type, such as consent or contract.*)
LegalBasesHaveValidType ==
    \A l \in activeLegalBases: l.type \in LegalBasis.type

        
    
(*Rule 3: Breach Reporting Deadline
Guarantees that data breaches are reported within 72 hours of discovery.*)    
BreachReportedOnTime ==
    \A b \in breachesInProgress:
        (b.status = "Pending") => Within72Hours(b.breachTime, currentTime)
--------------------------------

THEOREM Spec => []TypeInvariant
THEOREM Spec => []AllProcessingIsLawful
THEOREM Spec => []LegalBasesHaveValidType
THEOREM Spec => []BreachReportedOnTime

=============================================================================
\* Modification History
\* Last modified Wed Sep 10 16:19:08 CEST 2025 by tianxiang.lu
\* Created Mon Sep 08 22:05:22 CEST 2025 by tianxiang.lu
