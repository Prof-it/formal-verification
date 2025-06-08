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
    }

    Block[] public blocks;
    uint256 public nextBlockId;

    event BlockAdded(uint256 id, string data, address author, uint256 timestamp);

    constructor() {
        // Initialize with a genesis block
        _addBlock("Genesis Block");
    }

    function addBlock(string memory _data) public {
        _addBlock(_data);
    }

    function _addBlock(string memory _data) internal {
        blocks.push(Block(nextBlockId, _data, block.timestamp, msg.sender));
        emit BlockAdded(nextBlockId, _data, msg.sender, block.timestamp);
        nextBlockId++;
    }

    function getBlock(uint256 _id) public view returns (uint256, string memory, uint256, address) {
        require(_id < blocks.length, "Block does not exist");
        Block storage b = blocks[_id];
        return (b.id, b.data, b.timestamp, b.author);
    }

    function getLatestBlock() public view returns (uint256, string memory, uint256, address) {
        require(blocks.length > 0, "No blocks in the chain");
        Block storage b = blocks[blocks.length - 1];
        return (b.id, b.data, b.timestamp, b.author);
    }

    function getBlockCount() public view returns (uint256) {
        return blocks.length;
    }
}
