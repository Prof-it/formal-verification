const hre = require("hardhat");

async function main() {
  const [deployer] = await hre.ethers.getSigners();

  console.log("Deploying contracts with the account:", deployer.address);
  console.log("Account balance:", (await hre.ethers.provider.getBalance(deployer.address)).toString());

  const Blockchain = await hre.ethers.getContractFactory("Blockchain");
  const blockchain = await Blockchain.deploy();

  // await blockchain.deployed(); // deprecated
  await blockchain.waitForDeployment();

  console.log("Blockchain contract deployed to:", await blockchain.getAddress());
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
