#!/usr/bin/env node
// Extracts every package in corpus/.cache/packages.json into corpus/.cache/packages/<name>@<version>/ against its
// registry integrity, then writes the generated tsconfig.json and olint.config.json olint analyses it with.
//
// pacote extracts registry tarballs without running lifecycle scripts; `ignoreScripts` also covers its directory and
// git fetchers, which the exact `name@version` specs here never reach. A package whose recorded integrity matches
// corpus/.cache/fetched.json and whose directory exists is not extracted again; its generated files are rewritten.
import { existsSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import path from "node:path";
import pacote from "pacote";
import {
	cacheDir,
	isSourcePath,
	mapPool,
	packageDir,
	packagesPath,
	SOURCE_EXTENSIONS,
	stableJson,
	stringLeaves,
	withRetries,
} from "./common.mjs";

const CONCURRENCY = 8;
const ATTEMPTS = 4;
const fetchedPath = path.join(cacheDir, "fetched.json");

// Declaration files are excluded: olint selects a sibling `index.d.ts` over `index.js`, which leaves a package that
// ships its own typings with no analysed function bodies.
const tsconfig = {
	compilerOptions: { allowJs: true, checkJs: false, noEmit: true },
	include: SOURCE_EXTENSIONS.map((extension) => `**/*${extension}`),
	exclude: ["**/*.d.ts", "**/*.d.mts", "**/*.d.cts", "node_modules"],
};

function isFile(file) {
	return existsSync(file) && statSync(file).isFile();
}

function resolvedEntry(dir, target, extensionless) {
	const relative = path.posix.normalize(target.replaceAll("\\", "/"));
	if (relative.startsWith("../") || path.posix.isAbsolute(relative) || relative.includes("*")) return undefined;
	const candidates = extensionless
		? [relative, `${relative}.js`, `${relative}/index.js`].map((file) => path.posix.normalize(file))
		: [relative];
	return candidates.find((file) => isSourcePath(file) && isFile(path.join(dir, file)));
}

function entrypointsOf(dir) {
	const manifest = JSON.parse(readFileSync(path.join(dir, "package.json"), "utf8"));
	const fromExports = manifest.exports !== undefined && manifest.exports !== null;
	const targets = fromExports ? stringLeaves(manifest.exports) : [manifest.main ?? "index.js"];
	const entries = targets.map((target) => resolvedEntry(dir, target, !fromExports)).filter(Boolean);
	return [...new Set(entries)];
}

function writeGenerated(dir) {
	const entrypoints = entrypointsOf(dir);
	writeFileSync(path.join(dir, "tsconfig.json"), stableJson(tsconfig));
	writeFileSync(path.join(dir, "olint.config.json"), stableJson(entrypoints.length > 0 ? { entrypoints } : {}));
}

function writeFetched() {
	const sorted = Object.fromEntries(Object.entries(fetched).sort(([left], [right]) => (left < right ? -1 : 1)));
	writeFileSync(fetchedPath, stableJson(sorted));
}

const packages = JSON.parse(readFileSync(packagesPath, "utf8"));
const fetched = existsSync(fetchedPath) ? JSON.parse(readFileSync(fetchedPath, "utf8")) : {};
const failures = [];
let extracted = 0;
const started = Date.now();

await mapPool(packages, CONCURRENCY, async ({ name, version, integrity, tarball }) => {
	const key = `${name}@${version}`;
	const dir = packageDir(name, version);
	try {
		if (fetched[key] !== integrity || !isFile(path.join(dir, "package.json"))) {
			delete fetched[key];
			rmSync(dir, { recursive: true, force: true });
			await withRetries(key, ATTEMPTS, () =>
				pacote.extract(key, dir, { integrity, resolved: tarball, ignoreScripts: true }),
			);
			fetched[key] = integrity;
			if (++extracted % 50 === 0) writeFetched();
		}
		writeGenerated(dir);
	} catch (error) {
		failures.push(`${key}: ${error.message}`);
	}
});

writeFetched();
console.error(
	`extracted ${extracted}, reused ${packages.length - extracted - failures.length}, failed ${failures.length} in ${Math.round((Date.now() - started) / 1000)}s`,
);
for (const failure of failures) console.error(`failed ${failure}`);
process.exitCode = failures.length > 0 ? 1 : 0;
