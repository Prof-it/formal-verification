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
- **Accurate Date Logic**: The model correctly accounts for varying month lengths and leap years when calculating time differences, ensuring that temporal rules like the 72-hour incident deadline are verified correctly.

### 3. Integrated DPV Concepts
The model's data structures are built around key concepts from the DPV (Data Privacy Vocabulary) ontology. This ensures the specification is semantically aligned with established data privacy standards.

- **`LegalBasis` Records**: Structured records represent the different legal bases, each with a subject, data type, and temporal bounds.
- **`Process` Records**: Processing activities are modeled with clear start and end times, allowing for lifecycle management.

***

## GDPR Rules Implemented

The model implements and formally verifies the following core GDPR principles:

- **Legal Basis Requirement (R1)**: Verifies that all active data processing has a valid legal basis.
- **Legal Basis Types (R2)**: Models different legal basis types (Consent, Contract, etc.).
- **Incident Reporting Deadline (R3)**: Guarantees that data incidents are reported within 72 hours of discovery.

***

## Model Structure

### Constants
- **`DataSubjects`**: The set of persons.
- **`Data`**: The set of data types being processed.
- **`EventTypes`**: The set of event types that can trigger state changes (e.g., `StartProcessing`, `GiveConsent`, `StartContract`).

### Variables
- **`now`**: The current system time, which advances with each event.
- **`events`**: A set of pending events waiting to be executed.
- **`processes`**: The set of all currently running data processing activities.
- **`legalBases`**: The set of all currently active legal bases.
- **`incidents`**: The set of recorded data incidents awaiting action.

### Actions
- **Event Actions**: **`GiveConsent`**, **`WithdrawConsent`**, **`StartContract`**, **`EndContract`**, and **`StartProcessing`** are all triggered by events in `events`. These actions modify the system state in response to external events.
- **State-Driven Actions**: **`ComplianceIncident`** and **`ReportIncident`** are triggered when system conditions are met, such as when a legal basis expires or a processing activity becomes unlawful.

***

## Usage and Verification

To verify the model:

1.  **Open the specification** in the TLA+ Toolbox.
2.  **Define the concrete test scenario** in the `MC_GDPR_Time` module, where you provide specific values for **`DataSubjects`**, **`Data`**, and **`InitialEvents`**. For easy start up, we already provided a scenario with the specific values in **`MC_xxx`** definitions, you only need to assign the **`MC_xxx`** as the model values for the constants correspondingly. 

3. Run TLC Model Checker  

Use **TLC** to verify invariants in the TLA+ model.  

- The model defines `Spec` as the main specification.  
- GDPR rules (`TypeInvariant`, `AllProcessingIsLawful`, `LegalBasesHaveValidType`, `IncidentReportedOnTime`) are listed in **`MC_GDPR_Time.cfg`**, so TLC will automatically check them as invariants.  

### Download TLC  
TLC is part of the [TLA+ Tools](https://github.com/tlaplus/tlaplus/releases).  
Download the latest `tla2tools.jar` and place it in your working directory.  

### Run from CLI  

```bash
# Run with default configuration (MC_GDPR_Time.cfg will be used automatically)
java -cp tla2tools.jar tlc2.TLC MC_GDPR_Time.tla

# Explicitly specify the config file (optional)
java -cp tla2tools.jar tlc2.TLC MC_GDPR_Time.tla -config MC_GDPR_Time.cfg

# Limit exploration depth (optional)
java -cp tla2tools.jar tlc2.TLC -depth 100 MC_GDPR_Time.tla
```
### Sample TLC Output

TLC2 Version 2.18 of 01 August 2025
Running model checking with 4 worker threads.

Parsing file MC_GDPR_Time.tla
Parsing file MC_GDPR_Time.cfg
Semantic processing of MC_GDPR_Time
Starting... 

Progress(202 states generated, 56 distinct states, 0 states left on queue.)
Checking invariants:
  TypeInvariant               OK
  AllProcessingIsLawful       OK
  LegalBasesHaveValidType     OK
  IncidentReportedOnTime        OK

Model checking completed. No error has been found.

Our current defined scenario is a violation of GDPR, so you should see some violation trace, but if you only put TypeInvariant, you should see it checks successfully.

## Compatibility with Data Privacy Vocabulary (DPV)  
Based on the W3C Community Standard: [w3c.github.io/dpv](https://w3c.github.io/dpv/)  

We use the **DPV Ontology** with [Protégé](https://protege.stanford.edu/):  
- **dpv-owl.rdf** — initial ontology for our model  
- **eu-gdpr-owl.rdf** — extended ontology for EU GDPR  
- **dpv-owl-turtle** — Turtle export of our model from Protégé  

*Files downloaded June 2025; check [DPV](https://w3c.github.io/dpv/) for updates.*  

### Visualization & Reasoning with Ontology
- Explore entities and relationships with Protégé’s **OntoGraf**  
- Use Protégé plugins for description logic reasoning, validation, and SPARQL queries  
# trace2vis Visualization Tool

The `trace2vis` subfolder contains scripts to visualize TLC traces from GDPR TLA+ models as Mermaid Gantt charts. This helps in understanding event timelines, legal basis validity, and compliance periods.

### Usage

1. Install dependencies:
   ```
   pip install -r trace2vis/requirements.txt
   ```
2. Run the visualizer on a TLC `.out` file:
   ```
   cd trace2vis
   python trace2mermaid.py ../MC_GDPR_Consentwithdrawn.out -o timeline.mmd
   # or use trace2mermaid_llm.py for LLM-based diagrams
   ```
3. Open `timeline.mmd` in [Mermaid Live Editor](https://mermaid.live) to view the diagram.

### Requirements

See [`trace2vis/requirements.txt`](trace2vis/requirements.txt) for all dependencies.

### Testing

Run tests in the `trace2vis` folder with:
```
pytest
```
