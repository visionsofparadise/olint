import { spawnSync } from "node:child_process";

const installed = spawnSync("cargo", ["sweep", "--version"], { stdio: "ignore" }).status === 0;

if (installed) process.exit(spawnSync("cargo", ["sweep", "--time", "14"], { stdio: "inherit" }).status ?? 1);

console.log("cargo-sweep is not installed; skipping target cleanup (cargo binstall cargo-sweep).");
