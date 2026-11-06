# Evaluable rules for externally effective agent actions

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24014599.svg)](https://doi.org/10.5281/zenodo.24014599)

Seven rules for governing actions that AI agents take outside the system (approving, paying, writing to another system). Each rule is written two ways:

- in **plain language**, so that people without a formal-methods background can read, review and apply it;
- as a **formal reading** in temporal logic and TLA+, so that it can be checked automatically against recorded logs or with the TLC model checker.

The design goal is that every rule can be decided from a finite evidence record: if a rule is broken, the log shows it.

> **Disclaimer.** This is personal work by Dr. Tianxiang Lu. It was prepared as input to discussions in the IEEE P7022 working group, but it is not an IEEE SA document and is not endorsed by IEEE, IEEE SA or any working group.

## Three rule types

| Type | Template | Can a record show a breach? |
| --- | --- | --- |
| A. Always rule | Whenever ⟨event⟩ happens, ⟨condition⟩ holds. | Yes: a single record shows it. |
| B. Order rule | ⟨Event⟩ never happens before / after ⟨event⟩. | Yes: the order of records shows it. |
| C. Deadline rule | After ⟨event⟩, ⟨event⟩ happens within ⟨time⟩. | Yes: once the time has passed. |
| Not usable | After ⟨event⟩, ⟨event⟩ eventually happens. | No: no record can ever show it. |

The templates are a subset of the property specification patterns of Dwyer, Avrunin and Corbett (ICSE 1999) and the bounded-response pattern of Konrad and Cheng (ICSE 2005).

## The seven rules

Events: `propose`, `authorize`, `revoke` / `expire`, `trigger` (re-check required), `record` (decision record committed), `effect` (action takes effect outside the system), `dispose` (deny, escalate, defer or safe state), `verify`.

| ID | Rule | Type | Formal reading |
| --- | --- | --- | --- |
| P1 Binding | Whenever an action takes effect, its action type, target and approved parameters match its approval. | A | `□( effect(a,k) ⇒ bound(a,k) )` |
| P2 Validity | An action never takes effect before its approval is issued, nor after that approval is revoked, expires or is re-opened by a trigger. | B | `( ¬effect(_,k) W authorize(_,k) ) ∧ □( invalidate(k) ⇒ □¬effect(_,k) )` |
| P3 No duplicates | The same protected effect never occurs twice. | A | `□( effects(u) ≤ 1 )` |
| P4 Record first | An action never takes effect before its decision record is committed. | B | `¬effect(a,_) W record(a)` |
| P5 Checks in place | Whenever an action takes effect, the required assurance, evidence and identity checks are in place. | A | `□( effect(a,k) ⇒ assured )` |
| R1 Every request gets an outcome | After an action is proposed, it takes effect or receives a recorded outcome within a declared time. | C | `□( propose(a) ⇒ ◇≤T ( effect(a,_) ∨ dispose(a,_) ) )` |
| R2 Effects are checked | After an action takes effect, its result is verified within a declared time. | C | `□( effect(a,k) ⇒ ◇≤T verify(a) )` |

Symbols: □ always; W weak until; ◇≤T within time T; ⇒ implies. `invalidate(k)` = `revoke(k) ∨ expire(k) ∨ trigger(k)`.

## Files

| File | Content |
| --- | --- |
| `AgentActionRules.tla` | The seven rules as TLA+ operators over an evidence log (a sequence of event records). Usable for trace checking of recorded logs. |
| `AgentActionBoundary.tla` | A minimal, illustrative execution-boundary model that writes such a log. Not a reference implementation. |
| `AgentActionBoundary_ok.cfg` | Correct boundary: an action takes effect only while checks are in place. |
| `AgentActionBoundary_failopen.cfg` | Fail-open boundary: an action can take effect while checks are down. |

## Running the model checker

```bash
java -cp tla2tools.jar tlc2.TLC -config AgentActionBoundary_ok.cfg AgentActionBoundary.tla
java -cp tla2tools.jar tlc2.TLC -config AgentActionBoundary_failopen.cfg AgentActionBoundary.tla
```

Results with TLC (1 action, T = 1, 3 time steps):

| Configuration | Result |
| --- | --- |
| Correct boundary | All seven rules hold; 5,036 distinct states explored exhaustively. |
| Fail-open boundary | P5 is breached; TLC returns a 6-step counterexample in which every step looks legitimate on its own. |

With two concurrent actions the state space grows beyond 9 million states; larger configurations need symmetry reduction, smaller bounds, or trace checking instead.

## Related work

- T. Lu, R. Kneuper, U. John and P. Beenken, "A TLA+ Approach to Verifiable Temporal Compliance of Event-Driven Systems: A GDPR Case Study", ICC'27 (accepted). See [`../../gdpr`](../../gdpr).
- T. Lu, "Verifier-Guided Repair of LLM-Generated TLA+ Specifications: A Skill-Mediated Agentic Loop for NASA DDMR-26", IEEE ETECOM 2026. See [`../../agentic_loop`](../../agentic_loop).
- T. Lu, "Neural-Symbolic Verification of Blockchain-Enabled IoT Systems via Refinement Mapping in TLA+", IEEE SmartNets 2026, [doi:10.1109/SmartNets69662.2026.11604597](https://doi.org/10.1109/SmartNets69662.2026.11604597).

## How to cite

> T. Lu, *Evaluable rules for externally effective agent actions* (version 1.0), Zenodo, 2026. doi:[10.5281/zenodo.24014599](https://doi.org/10.5281/zenodo.24014599)

Citation metadata: [`CITATION.cff`](CITATION.cff).

## Licence

Copyright (c) 2026 Dr. Tianxiang Lu. Licensed under the [Apache License, Version 2.0](LICENSE): free to use, including commercially, provided that the copyright notice and the [`NOTICE`](NOTICE) file with the citation are kept in all copies and derivative works.

This folder is an exception to the repository's non-commercial licence.
