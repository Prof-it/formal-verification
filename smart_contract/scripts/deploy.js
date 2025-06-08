const hre = require("hardhat");

async function main() {
  const [deployer] = await hre.ethers.getSigners();

  console.log("Deploying contracts with the account:", deployer.address);
  console.log("Account balance:", (await hre.ethers.provider.getBalance(deployer.address)).toString());

  const AnomalyAlert = await hre.ethers.getContractFactory("AnomalyAlert");
  console.log("Deploying AnomalyAlert...");
  const anomalyAlert = await AnomalyAlert.deploy();

  await anomalyAlert.waitForDeployment();

  console.log("AnomalyAlert contract deployed to:", await anomalyAlert.getAddress());
  console.log("Transaction hash:", anomalyAlert.deploymentTransaction().hash);
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
