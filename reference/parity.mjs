import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repo = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const maxBuffer = 256 * 1024 * 1024;

const args = process.argv.slice(2);
const tsconfig = args.find((a) => !a.startsWith("--"));
const typesArg = args.find((a) => a.startsWith("--types="));
const types = typesArg ? typesArg.slice("--types=".length) : "oracle";

if (!tsconfig) {
	console.error("olint: usage: parity.mjs <tsconfig> [--types=oracle|syntactic]");
	process.exit(2);
}

const olintBin = path.join(repo, "target", "release", process.platform === "win32" ? "olint.exe" : "olint");
if (!fs.existsSync(olintBin)) {
	console.error("olint: build first with npm run build");
	process.exit(2);
}

const referenceResult = spawnSync("node", [path.join(repo, "reference", "perfLint.ts"), tsconfig, "--report", `--types=${types}`], {
	encoding: "utf8",
	maxBuffer,
});
const olintResult = spawnSync(olintBin, [tsconfig, "--report", `--types=${types}`], { encoding: "utf8", maxBuffer });

const reportFailure = (label, result) => {
	if (result.error) {
		console.error(`${label}: ${result.error.message}`);
		return true;
	}
	if (result.status !== 0) {
		console.error(result.stderr ?? "");
		return true;
	}
	return false;
};

const referenceFailed = reportFailure("reference", referenceResult);
const olintFailed = reportFailure("olint", olintResult);
if (referenceFailed || olintFailed) process.exit(2);

const referenceOut = referenceResult.stdout ?? "";
const olintOut = olintResult.stdout ?? "";

if (referenceOut === olintOut) process.exit(0);

const referenceLines = referenceOut.split("\n");
const olintLines = olintOut.split("\n");

if (referenceLines[0] !== olintLines[0]) console.log("header differs");

const histogramOf = (lines) => {
	const first = lines.indexOf("");
	if (first === -1) return [];
	const second = lines.indexOf("", first + 1);
	return lines.slice(first + 1, second === -1 ? lines.length : second);
};
if (histogramOf(referenceLines).join("\n") !== histogramOf(olintLines).join("\n")) console.log("histogram differs");

const rowPattern = /^(O\(.+?\))\s+(\S.*?)\s\s(\S+:\d+)$/;
const rowsOf = (lines) => {
	const first = lines.indexOf("");
	const second = first === -1 ? -1 : lines.indexOf("", first + 1);
	const rest = second === -1 ? [] : lines.slice(second + 1);
	const rows = new Map();
	let current = null;
	for (const line of rest) {
		if (line === "") {
			current = null;
			continue;
		}
		const match = rowPattern.exec(line);
		if (match) {
			const [, cost, name, location] = match;
			current = { cost, name, location, chain: [] };
			rows.set(`${name} ${location}`, current);
		} else if (current) {
			current.chain.push(line);
		}
	}
	return rows;
};

const referenceRows = rowsOf(referenceLines);
const olintRows = rowsOf(olintLines);

let rowsDiffer = 0;
let chainLinesDiffer = 0;
const keys = new Set([...referenceRows.keys(), ...olintRows.keys()]);
for (const key of keys) {
	const referenceRow = referenceRows.get(key);
	const olintRow = olintRows.get(key);
	const referenceCost = referenceRow?.cost ?? "(missing)";
	const olintCost = olintRow?.cost ?? "(missing)";
	const referenceChain = referenceRow?.chain ?? [];
	const olintChain = olintRow?.chain ?? [];
	const same = referenceCost === olintCost && referenceChain.join("\n") === olintChain.join("\n");
	if (same) continue;
	rowsDiffer += 1;
	console.log(`${key}  reference ${referenceCost}  olint ${olintCost}`);
	const chainLength = Math.max(referenceChain.length, olintChain.length);
	for (let i = 0; i < chainLength; i += 1) {
		const referenceLine = referenceChain[i] ?? "(missing)";
		const olintLine = olintChain[i] ?? "(missing)";
		if (referenceLine === olintLine) continue;
		chainLinesDiffer += 1;
		console.log(`  ${key}  reference: ${referenceLine}`);
		console.log(`  ${key}  olint:     ${olintLine}`);
	}
}

console.log(`${rowsDiffer} rows differ, ${chainLinesDiffer} chain lines differ`);
process.exit(1);
