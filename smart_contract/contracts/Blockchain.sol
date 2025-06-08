// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// Uncomment this line to use console.log
// import "hardhat/console.sol";

contract Blockchain {
    struct Block {
        uint256 id;
        string data;
        uint256 timestamp;
        address author;
        bytes32 previousHash;
        bytes32 blockHash;
    }

    Block[] public blocks;
    uint256 public nextBlockId; // Represents the ID for the *next* block to be added

    event BlockAdded(uint256 id, string data, address author, uint256 timestamp, bytes32 previousHash, bytes32 blockHash);

    constructor() {
        // Initialize with a genesis block
        // Genesis block has no previous hash (or a conventional 0x0)
        bytes32 genesisPrevHash = bytes32(0);
        bytes32 genesisHash = _calculateBlockHash(0, "Genesis Block", block.timestamp, msg.sender, genesisPrevHash);
        blocks.push(Block(0, "Genesis Block", block.timestamp, msg.sender, genesisPrevHash, genesisHash));
        emit BlockAdded(0, "Genesis Block", msg.sender, block.timestamp, genesisPrevHash, genesisHash);
        nextBlockId = 1;
    }

    function addBlock(string memory _data) public {
        _addBlock(_data);
    }

    function _calculateBlockHash(
        uint256 _id,
        string memory _data,
        uint256 _timestamp,
        address _author,
        bytes32 _previousHash
    ) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(_id, _data, _timestamp, _author, _previousHash));
    }

    function _addBlock(string memory _data) internal {
        require(blocks.length > 0, "Cannot add block if genesis block doesn't exist");
        Block storage latestBlock = blocks[blocks.length - 1];
        bytes32 previousHash = latestBlock.blockHash;
        
        uint256 newBlockId = nextBlockId;
        uint256 newTimestamp = block.timestamp;
        address newAuthor = msg.sender;

        bytes32 currentBlockHash = _calculateBlockHash(newBlockId, _data, newTimestamp, newAuthor, previousHash);

        blocks.push(Block(newBlockId, _data, newTimestamp, newAuthor, previousHash, currentBlockHash));
        emit BlockAdded(newBlockId, _data, newAuthor, newTimestamp, previousHash, currentBlockHash);
        nextBlockId++;
    }

    function getBlock(uint256 _id) public view returns (uint256 id, string memory data, uint256 timestamp, address author, bytes32 previousHash, bytes32 blockHash) {
        require(_id < blocks.length, "Block does not exist");
        Block storage b = blocks[_id];
        return (b.id, b.data, b.timestamp, b.author, b.previousHash, b.blockHash);
    }

    function getLatestBlock() public view returns (uint256 id, string memory data, uint256 timestamp, address author, bytes32 previousHash, bytes32 blockHash) {
        require(blocks.length > 0, "No blocks in the chain");
        Block storage b = blocks[blocks.length - 1];
        return (b.id, b.data, b.timestamp, b.author, b.previousHash, b.blockHash);
    }

    function getBlockCount() public view returns (uint256) {
        return blocks.length;
    }
}
