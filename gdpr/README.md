# GDPR Temporal Compliance in TLA+

## Overview

This directory contains a TLA+ model for checking selected **temporal** GDPR requirements against an observed event history. The requirements are:
- processing only during a valid legal basis (Art. 6(1));
- breach notification within 72 hours (Art. 33(1)).

Each scenario is a finite set of timestamped events (`ObservedEvents`). TLC replays them in timestamp order, explores every ordering of events that share a timestamp, and reports a counterexample trace when a formalised requirement is violated. Each trace is rendered as a timeline figure by a deterministic script (`trace2tikz/`).

The model checks only the requirements formalised below, over the event history it is given. It is not a general GDPR compliance checker (see [Scope and limitations](#scope-and-limitations)).


***

## Modules

| Module | Content |
|---|---|
| `TimeUtils.tla` | `TimePoint` records (year, month, day, hour, minute) and their conversion to minutes since 2020-01-01 (`ToMinutes`), with leap years handled in closed form. Also `Before`, `TimeBetween` (inclusive bounds), `Within72Hours`, `MinTime`, `MaxTime`. |
| `GDPR_Time.tla` | State, event-driven and state-driven actions, `Next`, `Spec`, `TypeInvariant`. |
| `GDPR_Rules.tla` | The GDPR requirements as safety properties (invariants). |
| `MC_GDPR_Time.tla` | Concrete constants and the six paper scenarios (`MC_ObervedEvent…`). |
| `MC_*.cfg` | One TLC configuration per scenario: which event set to use and which invariants to check. |
| `MC_Edge.tla` | Edge-case scenarios used as regression tests (calendar boundaries, re-granted consent, malformed log, simultaneous events). |

### State variables

| Variable | Meaning |
|---|---|
| `now` | Current time; set by each consumed event, or advanced by `TimeAdvance`. |
| `events` | Observed events not yet consumed. |
| `legalBases` | `Consent`/`Contract` records with start and end (`end = FixedEndTime` while open). |
| `processes` | Processing activities with start and end (processes end only at the observation horizon). |
| `breaches` | Detected breaches with status `Pending` or `Reported`. |
| `rejected` | Observed events that could not be applied in the current state. |

### Actions

**Event-driven.** These actions consume an event, and only an event with the earliest remaining timestamp (`e.time = MinTime(events)`):
- `GiveConsent` / `WithdrawConsent`: opens a consent, or closes the currently open consent for the same subject and data.
- `StartContract` / `EndContract`: the same for contracts.
- `StartProcessing`: opens a process.
- `DetectDataBreach` / `DataBreachReported`: creates a pending breach, or marks a matching pending breach as reported.
- `RejectEvent`: consumes an event whose precondition does not hold, e.g. a withdrawal without an open consent, and records it in `rejected`. This prevents a malformed log from silently blocking the rest of the replay.

**State-driven:**
- `TerminateProcess`: removes, in one step, every process whose end time has been reached (only at the horizon, since processes have no other end).
- `TimeAdvance`: moves `now` to the next event time. Once the log is exhausted, it moves `now` to the end of the observation horizon (`FixedEndTime`, 2500-12-31 23:59). This last step exposes violations that are never resolved, such as an unreported breach or processing that continues after consent ended.
- `RemoveUnreachableEvents`: drops events after the horizon.

***

## Requirements checked (`GDPR_Rules.tla`)

| Invariant | Requirement |
|---|---|
| `AllProcessingIsLawful` | Every active process has a legal basis for the same subject and data that is valid at `now` (Art. 6(1)); validity bounds are inclusive. |
| `LegalBasesHaveValidType` | Every legal basis is a `Consent` or a `Contract`. |
| `BreachReportedOnTime` | A pending breach is at most 72 h old, and a reported breach was reported within 72 h of detection (Art. 33(1)). |
| `NoRejectedEvents` | Every observed event could be applied. If this fails, the log is malformed or out of order and the other verdicts must not be trusted. |
| `TypeInvariant` | All variables have their declared types. |

The invariants are normative properties, not facts about the system. TLC is used to *find* behaviours that violate them, and each violation is returned as a trace. The model detects violations; it does not model their remediation.

***

## Event semantics

- **Order.** Events are replayed in timestamp order, regardless of their position in the log.
- **Simultaneous events.** Events with the same timestamp (one-minute resolution) are applied in every possible order. A property is reported as violated if *some* ordering violates it, which is a conservative semantics. Example: a consent and a processing start in the same minute produce a counterexample in which processing comes first.
- **Duplicates.** `ObservedEvents` is a set, so two entries that agree in type, time, subject and data are merged. Logs that can contain such duplicates need an event identifier.
- **Time zone.** Timestamps are assumed to be normalised (e.g. to UTC) before they enter the model.

***

## Scenarios and results

TLC 1.8.0, one worker; every run finishes in about 1 s.

| Config | Invariants | Result | Distinct states |
|---|---|---|---|
| `MC_ValidConsent.cfg` | `AllProcessingIsLawful`, `TypeInvariant` | holds | 6 |
| `MC_ReportBreachNoViolation.cfg` | `BreachReportedOnTime`, `TypeInvariant` | holds | 10 |
| `MC_MissingConsent.cfg` | `AllProcessingIsLawful`, `TypeInvariant` | violated (state 2, at `StartProcessing`) | 2 |
| `MC_ConsentWithdrawn.cfg` | `AllProcessingIsLawful`, `TypeInvariant` | violated (state 5, `TimeAdvance` to horizon) | 7 |
| `MC_DeadlineViolation.cfg` | `BreachReportedOnTime`, `TypeInvariant` | violated (state 5, 72 h + 1 min after detection) | 7 |
| `MC_ReportBreachLate.cfg` | `BreachReportedOnTime`, `TypeInvariant` | violated (state 5, report after 73.5 h) | 7 |
| `MC_GDPR_Time.cfg` | `TypeInvariant` only (valid-consent scenario) | holds | 6 |

In `MC_DeadlineViolation`, the second `GiveConsent` event at 07-15 08:31 only advances the clock past the deadline. The violation would also be found without it, at the horizon.

***

## Usage

Get `tla2tools.jar` from the [TLA+ releases](https://github.com/tlaplus/tlaplus/releases); the commands below assume it is in `../tla_modules/`.

```bash
# one scenario
java -cp ../tla_modules/tla2tools.jar tlc2.TLC MC_GDPR_Time.tla -config MC_ConsentWithdrawn.cfg

# write the counterexample as JSON as well (input for trace2tikz)
java -cp ../tla_modules/tla2tools.jar tlc2.TLC MC_GDPR_Time.tla -config MC_ConsentWithdrawn.cfg \
     -dumpTrace json MC_ConsentWithdrawn.json
```
TLC exits with a non-zero code when an invariant is violated; for the four violation scenarios this is the expected outcome.

To add a scenario:
1. Define a new event set in `MC_GDPR_Time.tla`, following the existing `MC_ObervedEvent…` definitions.
2. Copy a `.cfg` file and point `ObservedEvents` at the new set.
3. Choose the invariants to check.

### Checking an event log

`tools/check_log.py` is the ingestion step from a log to TLC. It:
1. validates the events (known type, minute-resolution timestamp, year 2020–2500, duplicates reported);
2. writes them as `ObservedEvents` into a generated module;
3. runs TLC, by default once per (subject, data) projection and in parallel.

```bash
# a JSON log: [{"type": "GiveConsent", "time": "2025-07-12 08:20", "subject": "erni", "data": "emaildata"}, ...]
python3 tools/check_log.py log.json --jar ../tla_modules/tla2tools.jar

# one of the scenarios in MC_GDPR_Time.tla; keep the counterexamples for trace2tikz
python3 tools/check_log.py --scenario MC_ObervedEventDeadlineViolation \
        --jar ../tla_modules/tla2tools.jar --traces traces/

# whole log in one run (needed for properties that relate several pairs)
python3 tools/check_log.py log.json --jar ../tla_modules/tla2tools.jar --no-project
```
Timestamps must be in UTC with format `YYYY-MM-DD HH:MM`. By default the invariants `NoRejectedEvents`, `AllProcessingIsLawful`, `BreachReportedOnTime` and `TypeInvariant` are checked; select others with `--invariants`. The exit code is 0 if all hold, 1 on a violation and 2 on an error.

How the two modes differ in what they report:
- TLC stops at the first violation of a run, so `--no-project` reports one violation for the whole log, while projection reports one per violating pair.
- The violating *state* can differ. In the whole log, an unrelated event may advance `now` past a deadline earlier; in the projection, the same violation is found at the next event of the pair or at the horizon. The verdict is the same.

### Timeline figures (`trace2tikz/`)

```bash
trace2tikz/make_figures.sh ../tla_modules/tla2tools.jar report   # -> report/MC_*.pdf
```
For each violation scenario, the script:
1. runs TLC with `-dumpTrace json`;
2. converts the trace with `trace2tikz.py`;
3. compiles the result with `pdflatex`.

Requirements: Python 3.9+ (standard library only) and a LaTeX installation with TikZ and `mathptmx`.

Everything in a figure is computed from the trace:
- event milestones are the events consumed between consecutive states;
- bars are the legal bases, processes and breaches of the final state;
- hatched intervals are processing without a legal basis, or a breach pending beyond its deadline;
- the dashed line is the 72 h deadline;
- the red line is the state in which TLC reports the violation.

The axis is ordinal: time points are equally spaced and labelled with their real timestamps, because the scenarios span minutes, days and the horizon.

### Tests

```bash
./regression_test.sh ../tla_modules/tla2tools.jar             # scenarios, edge cases, calendar check, figures
```
`regression_test.sh` checks every scenario configuration against its expected verdict, then runs the edge cases, the calendar check and `trace2tikz/make_figures.sh`; it exits with 0 only if all verdicts match. TLC output goes to `out/`, figures to `trace2tikz/report/`. Use `--no-figures` without a LaTeX installation.

Individual checks:

```bash
J=../tla_modules/tla2tools.jar
./run_edge_cases.sh $J                                        # edge cases, expected verdicts
python3 tools/check_timeutils.py . $J                         # ToMinutes vs Python datetime, 314 dates
python3 tools/diff_projection.py --jar $J --wellformed        # whole log vs projections, random logs
python3 gen_scale.py --sweep 5,10,20,40 --jar $J              # scaling, distinct timestamps
python3 gen_scale.py --sweep 4,8,12 --mode ties --jar $J      # scaling, simultaneous events
python3 gen_scale.py --sweep 5,10,20,40 --mode unlawful --jar $J   # scaling, processing without legal basis
python3 gen_scale.py 12 ties --json ties12.json               # same benchmark as a log for check_log.py
```
- `check_timeutils.py` lets TLC evaluate `ToMinutes` from this `TimeUtils.tla` on random and boundary dates between 2020 and 2500, and compares the results with Python's `datetime`.
- `gen_scale.py` writes `MC_Scale.tla` and `MC_Scale.cfg` for each size and runs TLC. In `seq` and `ties` modes the logs are compliant; in `unlawful` mode no processing has a legal basis, and the sweep checks `NoRejectedEvents`, which holds, so that TLC explores the whole state space.
- `diff_projection.py` generates random logs with 2–3 pairs, ties within and across pairs, and timestamps around the 72 h boundary. For each invariant separately, it checks that the whole-log verdict equals the disjunction of the projection verdicts. Without `--wellformed` the logs are uniformly random, and most of them are malformed; `--lawful 0.8` makes most pairs lawful, so that the cases where `AllProcessingIsLawful` holds are also covered.

***

## Scalability

- **Distinct timestamps.** TLC follows a single replay path and the state count grows linearly with the log, whether or not it is compliant. Compliant logs (`gen_scale.py`) of 10, 40, 160 and 320 events give 22, 82, 322 and 642 distinct states; logs of 5, 10, 20 and 40 processing events without any legal basis (`--mode unlawful`, checked against `NoRejectedEvents` so that TLC explores everything) give 12, 22, 42 and 82.
- **Simultaneous events.** A group of *k* events with the same timestamp yields 2^k intermediate states (every subset of the group already applied); two groups of 12 give 8,194 states, two groups of 14 give 32,770.

Earlier versions also contained incident actions (`ComplianceIncident`, `RecordIncident`) that recorded unlawful processing and terminated the process. They could fire at every time point and in any order, so a log with unlawful processing did not finish: a 7-event log passed 800,000 states, and even 5 unlawful processing events did not complete within 120 s. No invariant depended on them, so they were removed; the same 7-event log now takes 16 states.


Most of the interleavings between simultaneous events are irrelevant. Every invariant in `GDPR_Rules.tla` relates only events and records of the same data subject and data item: legal bases, processes, breaches and the rejection of an event are all matched on (subject, data). The order of simultaneous events of *different* pairs therefore cannot change a verdict.

`tools/check_log.py` exploits this by checking each (subject, data) projection of the log in its own TLC run (see [Checking an event log](#checking-an-event-log)). Ties then remain only between events of the same pair. On the `ties` benchmark with 12 and 14 pairs, each projection has 6 distinct states, against 8,194 and 32,770 for the whole log.

The cost is one TLC start (about 1 s of JVM start-up) per pair, run in parallel with `--jobs`. With few pairs, the whole-log run can therefore be faster in wall time: on the benchmark, projection is slower for 12 pairs (24 s vs 14 s) and faster from about 14 pairs (28 s vs 40 s).

The decomposition is sound only for per-pair properties. A property that relates several data subjects, e.g. one breach notification covering many affected subjects, must be checked with `--no-project`. Equivalence of the verdicts is tested on random logs by `tools/diff_projection.py`.

#### Projection Equivalence: Empirical Evidence

We tested the equivalence of whole-log and per-(subject, data) projection checking extensively using the `tools/diff_projection.py` utility. Example commands:

```bash
python3 tools/diff_projection.py --jar $J --logs 40 --seed 7              # uniform random logs
python3 tools/diff_projection.py --jar $J --logs 40 --seed 11 --wellformed
python3 tools/diff_projection.py --jar $J --logs 40 --seed 13 --wellformed --lawful 0.8
```
Each run generates 40 random logs, each with 2–3 subject/data pairs and events around the 72-hour boundary, and checks the invariants both on the whole log and each projection. Every invariant is checked in its own TLC run, so that stopping at the first violation (whole-log) cannot hide a difference in the outcomes.

**Results:**

| Batch | NoRejectedEvents violated / holds | AllProcessingIsLawful violated / holds | BreachReportedOnTime violated / holds | Mismatches |
|---|---|---|---|---|
| seed 7, random | 36 / 4 | 29 / 11 | 26 / 14 | 0 of 120 |
| seed 11, well-formed | 9 / 31 | 39 / 1 | 15 / 25 | 0 of 120 |
| seed 13, well-formed, `--lawful 0.8` | 7 / 33 | 10 / 30 | 20 / 20 | 0 of 120 |

In every batch, the verdict for each invariant on each log matched exactly between the whole-log and per-pair projections (0 mismatches of 120 comparisons in each case). This provides strong empirical confirmation that projection is sound **for this class of requirements**.

**Why this decomposition is safe:** Every invariant and event precondition in `GDPR_Rules.tla` relates only to records of the same (subject, data) pair. Thus, the order of simultaneous events from different pairs or their separation into individual projections cannot affect the verdict—provided the property does not span multiple pairs. For any property that does (e.g., one breach notification covering multiple subjects), use `--no-project`.

***

## Scope and limitations

- Only the requirements above are formalised. The risk exception and justified delay in Art. 33 are out of scope.
- Legal bases are matched per subject and data, not per **purpose**, although consent is purpose-specific (Art. 6(1)(a)).
- There is no `StopProcessing` or erasure event: processes end only at the horizon. Consequently, processing that correctly stops at a consent withdrawal cannot be expressed yet.
- The verdicts hold for the formalisation and the given event history. They assume the log is complete, correctly timestamped and correctly mapped to `ObservedEvents`.

***

## Data Privacy Vocabulary (DPV)
Based on the W3C Community Standard: [w3c.github.io/dpv](https://w3c.github.io/dpv/)

We use the **DPV Ontology** with [Protégé](https://protege.stanford.edu/):
- **dpv-owl.rdf**: initial ontology for our model
- **eu-gdpr-owl.rdf**: extended ontology for EU GDPR
- **dpv-owl-turtle**: Turtle export of our model from Protégé

*Files downloaded June 2025; check [DPV](https://w3c.github.io/dpv/) for updates.*

### Visualization & Reasoning with Ontology
- Explore entities and relationships with Protégé's **OntoGraf**.
- Use Protégé plugins for description logic reasoning, validation and SPARQL queries.

***

## Legacy: `trace2vis/`

`trace2vis/` contains the earlier Mermaid-based visualisation, kept for reference and no longer maintained:
- `trace2mermaid_llm.py` generates the chart with an LLM, so its output is not deterministic.
- `trace2mermaid.py` does not currently run.

Use `trace2tikz/` for figures derived from TLC traces.

***

## 📚 Publications

This repository accompanies the following research contributions:

* **Lu, T., Kneuper, R., John, U. and Beenken, P. (2027).** *A TLA+ Approach to Verifiable Temporal Compliance of Event-Driven Systems: A GDPR Case Study.* International Conference on Internet of Things, Data and Cloud Computing (ICC'27), Oxford, United Kingdom, 22–23 March 2027. **Accepted.**

* **Beenken, P., John, U., Kneuper, R. and Lu, T. (2026).** *Modeling Time-Dependent Rules in Data Protection Law for Automated Compliance Checking.* Post-Proceedings of the 2nd Workshop on Intelligent Digitalization, Évora, Portugal. Camera-ready.

```bibtex
@inproceedings{beenken2026modeling,
  author    = {Beenken, Philipp and John, Uwe and Kneuper, Ralf and Lu, Tianxiang},
  title     = {Modeling Time-Dependent Rules in Data Protection Law for Automated Compliance Checking},
  booktitle = {Post-Proceedings of the 2nd Workshop on Intelligent Digitalization},
  year      = {2026},
  address   = {Évora, Portugal},
  note      = {Camera-ready}
}
```
