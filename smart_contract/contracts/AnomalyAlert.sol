// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// For debugging during development with Hardhat, can be removed for production
// import "hardhat/console.sol"; 

contract AnomalyAlert {
    struct AnomalyEventData {
        bytes32 eventId;            // Unique hash of event details from the source
        address deviceId;           // Address or unique identifier of the IoT device
        uint256 detectionTimestamp; // Timestamp from the device when anomaly was detected
        string eventType;           // Type of anomaly (e.g., "temperature_high")
        bytes eventData;            // Additional flexible data about the event
        uint256 blockTimestamp;     // Blockchain timestamp when this event was processed
        address reporter;           // Address that submitted this event to the contract
    }

    // Mapping from the unique source event ID to confirm if an alert has been triggered
    mapping(bytes32 => bool) public hasAlertBeenTriggered;

    // Mapping from the unique source event ID to the stored event details
    // This provides on-chain transparency and allows querying details of processed anomalies
    mapping(bytes32 => AnomalyEventData) public recordedAnomalies;

    // Array to store all unique event IDs that have been processed
    // Useful for off-chain services to iterate or get a count
    bytes32[] public processedEventIds;

    event AnomalyReceived(
        bytes32 indexed eventId,
        address indexed deviceId,
        uint256 detectionTimestamp,
        string eventType,
        bytes eventData,
        address reporter
    );

    event AlertTriggered(
        bytes32 indexed eventId,
        address indexed deviceId,
        string eventType,
        string alertMessage
    );

    constructor() {
        // console.log("AnomalyAlert contract deployed by %s", msg.sender);
    }

    /**
     * @notice Processes a reported anomaly event from an IoT device or relay.
     * @dev Calculates a unique ID for the event based on its source characteristics to ensure idempotency.
     *      If the event is new, it's recorded, and an alert is triggered.
     * @param _deviceId The identifier of the device that detected the anomaly.
     * @param _detectionTimestamp The timestamp (from device) when the anomaly was detected.
     * @param _eventType A string categorizing the type of anomaly.
     * @param _eventData Additional binary data specific to the event.
     * @return eventId The unique ID generated and used for this event within the contract.
     */
    function processAnomaly(
        address _deviceId, // Using address for device ID for simplicity
        uint256 _detectionTimestamp,
        string memory _eventType,
        bytes memory _eventData
    ) public returns (bytes32 eventId) {
        // Calculate a unique event ID based on intrinsic properties of the source event.
        // This ensures that the same logical event from the device is treated as one, regardless of who reports it or when.
        eventId = keccak256(abi.encode(_deviceId, _detectionTimestamp, _eventType, _eventData));

        // Check for idempotency: if an alert for this eventId has already been triggered, revert.
        require(!hasAlertBeenTriggered[eventId], "AA:AlertAlreadyTriggered");

        // Mark that an alert is now being triggered for this eventId.
        hasAlertBeenTriggered[eventId] = true;

        // Store the detailed anomaly event data on-chain.
        recordedAnomalies[eventId] = AnomalyEventData({
            eventId: eventId,
            deviceId: _deviceId,
            detectionTimestamp: _detectionTimestamp,
            eventType: _eventType,
            eventData: _eventData,
            blockTimestamp: block.timestamp, // Record the blockchain timestamp of processing
            reporter: msg.sender            // Record who submitted this transaction
        });

        // Add the eventId to the list of all processed event IDs.
        processedEventIds.push(eventId);

        // Emit an event to log that the anomaly has been received and processed by the contract.
        emit AnomalyReceived(
            eventId,
            _deviceId,
            _detectionTimestamp,
            _eventType,
            _eventData,
            msg.sender
        );

        // Construct an alert message and emit the AlertTriggered event.
        string memory alertMessage = string(abi.encodePacked("Alert: Anomaly type '", _eventType, "' for device ", _addressToString(_deviceId), " detected at ", _uintToString(_detectionTimestamp)));
        emit AlertTriggered(
            eventId,
            _deviceId,
            _eventType,
            alertMessage
        );
        
        // console.log("Processed anomaly %s for device %s reported by %s", eventId, _addressToString(_deviceId), _addressToString(msg.sender));

        return eventId;
    }

    /**
     * @notice Retrieves the details of a previously recorded anomaly event.
     * @param _eventId The unique ID of the event to retrieve.
     * @return The AnomalyEventData struct containing all stored details for the event.
     */
    function getAnomalyDetails(bytes32 _eventId) public view returns (AnomalyEventData memory) {
        // Ensure the event has actually been processed before trying to return details.
        require(hasAlertBeenTriggered[_eventId], "AA:EventNotProcessed");
        return recordedAnomalies[_eventId];
    }
    
    /**
     * @notice Returns the total count of unique anomalies processed by the contract.
     */
    function getProcessedAnomaliesCount() public view returns (uint256) {
        return processedEventIds.length;
    }

    // --- Internal Helper Functions for string conversion ---
    function _addressToString(address _addr) internal pure returns (string memory) {
        bytes32 value = bytes32(uint256(uint160(_addr)));
        bytes memory alphabet = "0123456789abcdef";
        bytes memory str = new bytes(42);
        str[0] = '0';
        str[1] = 'x';
        for (uint i = 0; i < 20; i++) {
            str[2+i*2] = alphabet[uint(uint8(value[i + 12] >> 4))];
            str[3+i*2] = alphabet[uint(uint8(value[i + 12] & 0x0f))];
        }
        return string(str);
    }

    function _uintToString(uint256 _value) internal pure returns (string memory) {
        if (_value == 0) {
            return "0";
        }
        uint256 temp = _value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (_value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + _value % 10));
            _value /= 10;
        }
        return string(buffer);
    }
}
