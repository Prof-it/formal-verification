const { expect } = require("chai");
const { ethers } = require("hardhat"); // Use destructured ethers from hardhat

function calculateEventId(ethersInstance, deviceId, detectionTimestamp, eventType, eventData) {
    return ethersInstance.keccak256(
        ethersInstance.AbiCoder.defaultAbiCoder().encode(
            ["address", "uint256", "string", "bytes"],
            [deviceId, detectionTimestamp, eventType, eventData]
        )
    );
}

describe("AnomalyAlert", function () {
    let AnomalyAlertFactory;
    let anomalyAlert;
    let owner;
    let device1;
    let reporter1;
    let otherAccount;

    let device1Addr;
    let detectionTs;
    let eventType;
    let eventData;

    // 'before' hook for hreEthers initialization is removed

    beforeEach(async function () {
        device1Addr = "0x1234567890123456789012345678901234567890";
        detectionTs = Math.floor(Date.now() / 1000);
        eventType = "temperature_high";
        eventData = ethers.toUtf8Bytes("Sensor reading: 45C");

        AnomalyAlertFactory = await ethers.getContractFactory("AnomalyAlert");
        [owner, reporter1, otherAccount] = await ethers.getSigners();

        anomalyAlert = await AnomalyAlertFactory.deploy();
        await anomalyAlert.waitForDeployment();
    });

    describe("Deployment", function () {
        it("Should be deployed", async function () {
            expect(await anomalyAlert.getAddress()).to.not.be.null;
        });

        it("Should have processed zero anomalies initially", async function () {
            expect(await anomalyAlert.getProcessedAnomaliesCount()).to.equal(0);
        });
    });

    describe("Processing Anomalies", function () {
        let calculatedEventId;

        beforeEach(function() {
            calculatedEventId = calculateEventId(ethers, device1Addr, detectionTs, eventType, eventData);
        });

        it("Should allow processing a new anomaly", async function () {
            const tx = await anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData);
            await tx.wait();

            expect(await anomalyAlert.hasAlertBeenTriggered(calculatedEventId)).to.be.true;
            expect(await anomalyAlert.getProcessedAnomaliesCount()).to.equal(1);
            
            const storedAnomaly = await anomalyAlert.getAnomalyDetails(calculatedEventId);
            expect(storedAnomaly.eventId).to.equal(calculatedEventId);
            expect(storedAnomaly.deviceId).to.equal(device1Addr);
            expect(storedAnomaly.detectionTimestamp).to.equal(detectionTs);
            expect(storedAnomaly.eventType).to.equal(eventType);
            expect(storedAnomaly.eventData).to.equal(ethers.hexlify(eventData)); 
            expect(storedAnomaly.reporter).to.equal(reporter1.address);
        });

        it("Should emit AnomalyReceived and AlertTriggered events", async function () {
            const txPromise = anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData);

            await expect(txPromise)
                .to.emit(anomalyAlert, "AnomalyReceived")
                .withArgs(calculatedEventId, device1Addr, detectionTs, eventType, ethers.hexlify(eventData), reporter1.address);

            await expect(txPromise)
                .to.emit(anomalyAlert, "AlertTriggered")
                .withArgs(calculatedEventId, device1Addr, eventType, (args) => {
                    return args.includes(eventType) && args.includes(device1Addr.toLowerCase());
                });
        });

        it("Should prevent processing the exact same anomaly event twice (idempotency)", async function () {
            await anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData);
            
            await expect(
                anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData)
            ).to.be.revertedWith("AA:AlertAlreadyTriggered");

            await expect(
                anomalyAlert.connect(otherAccount).processAnomaly(device1Addr, detectionTs, eventType, eventData)
            ).to.be.revertedWith("AA:AlertAlreadyTriggered");
        });

        it("Should allow processing different anomaly events", async function () {
            await anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData);

            const newDetectionTs = detectionTs + 1;
            const newEventType = "pressure_low";
            const newEventData = ethers.toUtf8Bytes("Sensor reading: 0.8atm");
            const newCalculatedEventId = calculateEventId(ethers, device1Addr, newDetectionTs, newEventType, newEventData);

            await expect(anomalyAlert.connect(reporter1).processAnomaly(device1Addr, newDetectionTs, newEventType, newEventData))
                .to.emit(anomalyAlert, "AlertTriggered") 
                .withArgs(newCalculatedEventId, device1Addr, newEventType, (args) => args.includes(newEventType));
            
            expect(await anomalyAlert.getProcessedAnomaliesCount()).to.equal(2);
            expect(await anomalyAlert.hasAlertBeenTriggered(newCalculatedEventId)).to.be.true;
        });
    });

    describe("Retrieving Anomaly Details", function () {
        it("Should allow retrieval of processed anomaly details", async function () {
            const calculatedEventId = calculateEventId(ethers, device1Addr, detectionTs, eventType, eventData);
            await anomalyAlert.connect(reporter1).processAnomaly(device1Addr, detectionTs, eventType, eventData);

            const storedAnomaly = await anomalyAlert.getAnomalyDetails(calculatedEventId);
            expect(storedAnomaly.eventId).to.equal(calculatedEventId);
            expect(storedAnomaly.deviceId).to.equal(device1Addr);
        });

        it("Should revert when trying to retrieve details for an unprocessed event", async function () {
            const nonExistentEventId = calculateEventId(ethers, device1Addr, detectionTs + 100, "fake_event", eventData);
            await expect(anomalyAlert.getAnomalyDetails(nonExistentEventId))
                .to.be.revertedWith("AA:EventNotProcessed");
        });
    });
});
