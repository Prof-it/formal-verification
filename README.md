# Formal Verification of Modern Systems

This repository accompanies the book chapter on formal verification of modern systems, demonstrating the application of TLA+ across various domains:

- IoT Systems
- Peer-to-Peer Networks
- Blockchain Technology
- Quantum Protocols

## System Overview

The example system models a smart grid infrastructure that integrates:
1. Energy metering and anomaly detection at the edge
2. P2P network for secure communication
3. Blockchain for immutable audit trails
4. Quantum teleportation for secure information transfer

## Workflow

The formal verification process follows this workflow:

![Workflow Diagram](workflow/workflow.drawio.png)

## Module Structure

The system is divided into four main TLA+ modules:

1. `EnergyMeter.tla`
   - Edge device anomaly detection
   - State management and billing
   - Safety properties for meter operation

2. `P2PNetwork.tla`
   - Secure peer-to-peer communication
   - Message routing and delivery
   - Network reliability properties

3. `Blockchain.tla`
   - Immutable event recording
   - Smart contract execution
   - Audit trail maintenance

4. `QuantumTeleportation.tla`
   - Secure quantum information transfer
   - BB4P protocol implementation
   - Quantum state integrity

## Setup and Verification

### TLA+ Module Structure
Each TLA+ module follows this structure:

```tla
-------------------------------- MODULE ModuleName --------------------------------
EXTENDS Integers, Sequences, TLC, String, Nat

CONSTANTS YourConstants
VARIABLES YourVariables

Init == 
  /\ YourInitialConditions

Next == 
  YourNextStateRelation

Spec == Init \/ [][Next]_vars

=============================================================================
```

### Running TLC
1. Open TLA+ Toolbox
2. Create or open a specification:
   - Go to File → New → Specification
   - To verify a module, choose the module file
   - Enter the exact module name
   - Load the module and let the parser check it

3. Add all modules:
   - Right-click on the specification
   - Select "Add Module"
   - Add:
     - EnergyMeter.tla
     - P2PNetwork.tla
     - Blockchain.tla
     - QuantumTeleportation.tla

4. Create models for each module:
   - Right-click on each module
   - Select "New Model Using Module"
   - Name it appropriately (e.g., "EnergyMeter Model")
   - Click "OK"

5. Configure each model:
   - Click on the model in the left panel
   - In the right panel, click "Model Overview"
   - Set the following:
     - "What is the behavior spec?" → "Spec"
     - "What is the model checking task?" → "Check the temporal formula Spec"
     - "What temporal properties should be checked?" → Add all properties from the .cfg files
     - "What invariants should be checked?" → Add all invariants from the .cfg files

6. Run the verification:
   - Click the "Run Model" button (green play icon)
   - Wait for TLC to complete the verification
   - Check the results in the "Model Checking Results" tab

### Common Issues
- If TLC runs out of memory:
  - Increase the heap size in TLA+ Toolbox preferences
  - Set a larger value for "Maximum heap size (MB)"

- If state space is too large:
  - Use the "Finite State Space" option in model configuration
  - Limit the number of states to check
  - Use symmetry reduction if applicable

### Interpreting Results
- "No errors found" means all properties are satisfied
- "State space exhausted" means TLC couldn't explore all states
- "Counterexample found" indicates a property violation
- Check "Model Checking Results" for detailed information

### Debugging Tips
- Use the "Step" feature to manually explore states
- Add "Print" statements in your specification
- Use "Debug" mode to pause at specific states
- Check TLC statistics for performance issues

### TLA+ Best Practices
1. Use proper module headers and footers
2. Document your constants and variables
3. Use meaningful variable names
4. Keep specifications modular and reusable
5. Add comments for complex operations
6. Use type annotations where possible
7. Test with small models first
8. Use TLC statistics to optimize performance

## Key Properties Verified

- Type safety across all modules
- Anomaly detection and response
- Secure message delivery
- Immutable audit trails
- Quantum state preservation

## Directory Structure

- `tla_modules/` - Main TLA+ specification modules
- `tla_modules/tlc_configs/` - TLC model configuration files
- `workflow/` - System architecture diagrams


```bash
git clone https://github.com/yourusername/formal-verification.git
```

## Contributing

1. Create a new specification in the `specs` directory
2. Add model checking configurations in the `models` directory
3. Document your findings in the `docs` directory


## License

This software is licensed for NON-COMMERCIAL use only. For commercial use, please contact prof.dr.rer.nat.lu@gmail.com.

For more details, see the LICENSE file.
