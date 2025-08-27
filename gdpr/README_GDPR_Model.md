# GDPR Dynamic TLA+ Model

## Overview

This TLA+ specification models a dynamic system for GDPR compliance, focusing on the lifecycle of legal bases and data processing. It uses a temporal approach to formally verify key GDPR rules. The model is built to handle event-driven state changes and temporal constraints, providing a robust and flexible framework for compliance analysis.

***

## Key Features

### 1. Dynamic, Event-Driven Legal Bases
Instead of static constants, all legal bases (Consent and Contract) are now introduced into the system through specific events. This accurately reflects real-world scenarios where legal bases are established and change over time.

- **`GiveConsent`** event creates a new **`Consent`** legal basis.
- **`WithdrawConsent`** event dynamically updates the end time of a **`Consent`**.
- **`StartContract`** event creates a new **`Contract`** legal basis.
- **`EndContract`** event dynamically updates the end time of a **`Contract`**.

### 2. Enhanced Time Model
The **`TimeUtils`** module has been refined to provide a more robust and accurate time representation, preventing the logical errors and potential infinite loops that can arise from simplified date arithmetic.

- **Non-Recursive Time Calculation**: The time model uses a linear, non-recursive function to convert timestamps, which is crucial for TLC model checking to avoid stack overflows.
- **Accurate Date Logic**: The model correctly accounts for varying month lengths and leap years when calculating time differences, ensuring that temporal rules like the 72-hour breach deadline are verified correctly.

### 3. Integrated DPV Concepts
The model's data structures are built around key concepts from the DPV (Data Privacy Vocabulary) ontology. This ensures the specification is semantically aligned with established data privacy standards.

- **`LegalBasis` Records**: Structured records represent the different legal bases, each with a subject, data type, and temporal bounds.
- **`Process` Records**: Processing activities are modeled with clear start and end times, allowing for lifecycle management.

***

## GDPR Rules Implemented

The model implements and formally verifies the following core GDPR principles:

- **Legal Basis Requirement (R1)**: Verifies that all active data processing has a valid legal basis.
- **Legal Basis Types (R2)**: Models different legal basis types (Consent, Contract, etc.).
- **Consent Timing (R3)**: Ensures consent is valid for the entire duration of processing.
- **Contract Timing (R4)**: Verifies that contract-based processing only occurs within the contract's terms.
- **Breach Reporting Deadline (R5)**: Guarantees that data breaches are reported within 72 hours of discovery.

***

## Model Structure

### Constants
- **`DataSubjects`**: The set of persons.
- **`Data`**: The set of data types being processed.
- **`EventRecordTypes`**: The set of event types that can trigger state changes (e.g., `StartProcessing`, `GiveConsent`, `StartContract`).

### Variables
- **`currentTime`**: The current system time, which advances with each event.
- **`eventsToProcess`**: A set of pending events waiting to be executed.
- **`activeProcesses`**: The set of all currently running data processing activities.
- **`activeLegalBases`**: The set of all currently active legal bases.
- **`breachesInProgress`**: The set of recorded data breaches awaiting action.

### Actions
- **Event Actions**: **`GiveConsent`**, **`WithdrawConsent`**, **`StartContract`**, **`EndContract`**, and **`StartProcessing`** are all triggered by events in `eventsToProcess`. These actions modify the system state in response to external events.
- **State-Driven Actions**: **`BreachOccurs`** and **`ReportBreach`** are triggered when system conditions are met, such as when a legal basis expires or a processing activity becomes unlawful.

***

## Usage and Verification

To verify the model:

1.  **Open the specification** in the TLA+ Toolbox.
2.  **Define the concrete test scenario** in the `MC_GDPR_Time` module, where you provide specific values for **`DataSubjects`**, **`Data`**, and **`InitialEvents`**.
3.  **Run TLC** on the model to check all invariants. TLC will explore all possible sequences of events and state changes to prove that the GDPR rules are upheld in every reachable state.


## Compatibility with Data Privacy Vocabulary (DPV)  
Based on the W3C Community Standard: [w3c.github.io/dpv](https://w3c.github.io/dpv/)  

We use the **DPV Ontology** with [Protégé](https://protege.stanford.edu/):  
- **dpv-owl.rdf** — initial ontology for our model  
- **eu-gdpr-owl.rdf** — extended ontology for EU GDPR  
- **dpv-owl-turtle** — Turtle export of our model from Protégé  

*Files downloaded August 2025; check [DPV](https://w3c.github.io/dpv/) for updates.*  

### Visualization & Reasoning with Ontology
- Explore entities and relationships with Protégé’s **OntoGraf**  
- Use Protégé plugins for description logic reasoning, validation, and SPARQL queries  
