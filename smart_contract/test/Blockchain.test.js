const { expect } = require("chai");
const { ethers } = require("hardhat");

describe("Blockchain", function () {
  let Blockchain;
  let blockchain;
  let owner;
  let addr1;

  beforeEach(async function () {
    // Get the ContractFactory and Signers here.
    Blockchain = await ethers.getContractFactory("Blockchain");
    [owner, addr1] = await ethers.getSigners();

    // Deploy a new instance of the contract before each test.
    blockchain = await Blockchain.deploy();
    // await blockchain.deployed(); // deprecated
    await blockchain.waitForDeployment();
  });

  describe("Deployment", function () {
    it("Should have a genesis block", async function () {
      expect(await blockchain.getBlockCount()).to.equal(1);
      const [id, data, timestamp, author] = await blockchain.getBlock(0);
      expect(id).to.equal(0);
      expect(data).to.equal("Genesis Block");
      expect(author).to.equal(owner.address); // Genesis block author is the deployer
    });

    it("Should set the nextBlockId to 1 after deployment", async function () {
      expect(await blockchain.nextBlockId()).to.equal(1);
    });
  });

  describe("Adding Blocks", function () {
    it("Should allow users to add blocks", async function () {
      const blockData = "Test Block 1";
      await blockchain.connect(addr1).addBlock(blockData);
      expect(await blockchain.getBlockCount()).to.equal(2);

      const [id, data, timestamp, author] = await blockchain.getBlock(1);
      expect(id).to.equal(1);
      expect(data).to.equal(blockData);
      expect(author).to.equal(addr1.address);
    });

    it("Should emit a BlockAdded event when a block is added", async function () {
      const blockData = "Event Test Block";
      await expect(blockchain.connect(addr1).addBlock(blockData))
        .to.emit(blockchain, "BlockAdded")
        .withArgs(1, blockData, addr1.address, (await ethers.provider.getBlock('latest')).timestamp + 1); // Timestamp might be tricky due to block mining time
    });

     it("Should increment nextBlockId after adding a block", async function () {
      await blockchain.addBlock("Another Block");
      expect(await blockchain.nextBlockId()).to.equal(2);
    });
  });

  describe("Retrieving Blocks", function () {
    it("Should allow retrieval of existing blocks", async function () {
      const blockData = "Block for retrieval";
      await blockchain.addBlock(blockData);
      const [id, data, , author] = await blockchain.getBlock(1);
      expect(id).to.equal(1);
      expect(data).to.equal(blockData);
      expect(author).to.equal(owner.address);
    });

    it("Should revert if trying to get a non-existent block", async function () {
      await expect(blockchain.getBlock(5)).to.be.revertedWith("Block does not exist");
    });

    it("Should allow retrieval of the latest block", async function () {
      const blockData1 = "Block 1";
      const blockData2 = "Block 2 - Latest";
      await blockchain.addBlock(blockData1);
      await blockchain.connect(addr1).addBlock(blockData2);

      const [id, data, , author] = await blockchain.getLatestBlock();
      expect(id).to.equal(2); // Genesis, Block 1, Block 2
      expect(data).to.equal(blockData2);
      expect(author).to.equal(addr1.address);
    });

    it("Should revert if trying to get latest block when chain is empty (should not happen with genesis)", async function () {
        // This case is theoretically hard to hit with the current constructor logic (genesis block)
        // If the contract was deployable without a genesis block, this test would be more relevant.
        // For now, we test the existing state.
        const [id, data, , author] = await blockchain.getLatestBlock();
        expect(id).to.equal(0);
        expect(data).to.equal("Genesis Block");
    });
  });
});
