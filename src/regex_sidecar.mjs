import childProcess from "node:child_process";
import fs from "node:fs";
import { createRequire } from "node:module";
import workerThreads from "node:worker_threads";

const PROTOCOL_VERSION = 1;
const RECHECK_VERSION = "4.5.0";
const MALFORMED_REQUEST = 2;
const PACKAGE_UNAVAILABLE = 3;
const VERSION_MISMATCH = 4;
const FORBIDDEN_EXECUTION = 5;

const fail = (status, message) => {
	fs.writeSync(2, message);
	process.exit(status);
};

const input = JSON.parse(fs.readFileSync(0, "utf8"));
if (input.version !== PROTOCOL_VERSION) {
	fail(MALFORMED_REQUEST, `protocol version ${JSON.stringify(input.version)} where ${PROTOCOL_VERSION} is supported`);
}
if (!Number.isInteger(input.timeout) || input.timeout < 0) {
	fail(MALFORMED_REQUEST, `timeout ${JSON.stringify(input.timeout)} is not a non-negative integer`);
}
if (
	!Array.isArray(input.requests) ||
	!input.requests.every((request) => typeof request.source === "string" && typeof request.flags === "string")
) {
	fail(MALFORMED_REQUEST, "requests must be an array of source and flags strings");
}

process.env.RECHECK_BACKEND = "pure";
process.env.RECHECK_SYNC_BACKEND = "pure";
delete process.env.RECHECK_BIN;
delete process.env.RECHECK_JAR;

const sources = new Set(input.requests.map((request) => request.source));
let forbidden;
const forbid = (attempt) => {
	forbidden ??= attempt;
	throw new Error(`${attempt} is forbidden`);
};
for (const key of ["spawn", "spawnSync", "exec", "execSync", "execFile", "execFileSync", "fork"]) {
	childProcess[key] = () => forbid(`child_process.${key}`);
}
workerThreads.Worker = class {
	constructor() {
		forbid("worker_threads.Worker");
	}
};
const exec = RegExp.prototype.exec;
RegExp.prototype.exec = function (text) {
	if (sources.has(this.source)) forbid(`matching /${this.source}/`);
	return exec.call(this, text);
};

const require = createRequire(import.meta.url);
let manifestPath;
try {
	manifestPath = require.resolve("recheck/package.json");
} catch (error) {
	fail(
		PACKAGE_UNAVAILABLE,
		`recheck ${RECHECK_VERSION} is not installed beside ${import.meta.filename}: ${error.message}`,
	);
}
const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
if (manifest.version !== RECHECK_VERSION) {
	fail(VERSION_MISMATCH, `recheck ${manifest.version} at ${manifestPath} where ${RECHECK_VERSION} is required`);
}
const { checkSync } = createRequire(manifestPath)("./");

const parameters = { checker: "automaton", recallTimeout: -1, timeout: input.timeout, maxRecallStringSize: 128 };
const reply = (value) => fs.writeSync(1, JSON.stringify(value) + "\n");

reply({ version: PROTOCOL_VERSION, recheck: manifest.version });
for (const request of input.requests) {
	let diagnostics;
	try {
		diagnostics = checkSync(request.source, request.flags, { ...parameters });
	} catch (error) {
		if (forbidden === undefined) throw error;
	}
	if (forbidden !== undefined) fail(FORBIDDEN_EXECUTION, `${forbidden} was attempted while checking a pattern`);
	const complexity = diagnostics.complexity;
	reply({
		source: diagnostics.source,
		flags: diagnostics.flags,
		status: diagnostics.status,
		checker: diagnostics.checker ?? null,
		complexity:
			complexity === undefined
				? null
				: { type: complexity.type, degree: complexity.degree ?? null, isFuzz: complexity.isFuzz },
		error: diagnostics.error?.kind ?? null,
	});
}
