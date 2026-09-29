#!/usr/bin/env node
// Derives the package corpus deterministically from the selection parameters below and the exact-pinned
// npm-high-impact list, writing corpus/.cache/packages.json.
//
// Each listed package resolves to its highest release version published on or before CUTOFF, read from the
// registry packument's `time` field. A package enters the size population when that version's metadata points at
// JavaScript or TypeScript sources: it is outside `@types/`, its `dist.unpackedSize` is recorded, and its declared
// entries (`exports`, `main`, `module`, `bin`) include a source-extension or extensionless target, or it declares
// none and so defaults to `index.js`. The population is sorted by unpacked size and cut into BAND_COUNT
// equal-count quantile bands. Each band then takes its BAND_SIZE highest-impact packages whose tarball file listing
// ships a source file, so selection confirms "ships sources" against the tarball itself.
//
// Registry answers are cached in corpus/.cache/registry.json and tarball verdicts in corpus/.cache/listings.json;
// `--refresh` ignores both caches.
import { mkdirSync, readFileSync, writeFileSync, existsSync } from "node:fs";
import path from "node:path";
import { gunzipSync } from "node:zlib";
import pacote from "pacote";
import { npmHighImpact } from "npm-high-impact";
import {
	cacheDir,
	corpusDir,
	isSourcePath,
	mapPool,
	packagesPath,
	stableJson,
	stringLeaves,
	withRetries,
} from "./common.mjs";

const CUTOFF = "2026-09-29";
const BAND_COUNT = 5;
const BAND_SIZE = 200;

const REGISTRY = "https://registry.npmjs.org/";
const CONCURRENCY = 24;
const ATTEMPTS = 6;
const cutoffEnd = Date.parse(`${CUTOFF}T00:00:00.000Z`) + 24 * 60 * 60 * 1000;
const listVersion = JSON.parse(readFileSync(path.join(corpusDir, "..", "package.json"), "utf8")).devDependencies[
	"npm-high-impact"
];
const registryCachePath = path.join(cacheDir, "registry.json");
const listingCachePath = path.join(cacheDir, "listings.json");
const bandsPath = path.join(cacheDir, "bands.json");
const refresh = process.argv.includes("--refresh");
const RELEASE = /^(\d+)\.(\d+)\.(\d+)$/;

function readCache(file, key) {
	if (refresh || !existsSync(file)) return {};
	const cache = JSON.parse(readFileSync(file, "utf8"));
	return cache.key === key ? cache.entries : {};
}

function writeCache(file, key, entries) {
	const sorted = Object.fromEntries(Object.entries(entries).sort(([left], [right]) => (left < right ? -1 : 1)));
	writeFileSync(file, stableJson({ key, entries: sorted }));
}

function compareRelease(left, right) {
	for (let index = 0; index < 3; index++) if (left[index] !== right[index]) return left[index] - right[index];
	return 0;
}

function integrityOf(dist) {
	if (typeof dist.integrity === "string") return dist.integrity;
	if (typeof dist.shasum === "string") return `sha1-${Buffer.from(dist.shasum, "hex").toString("base64")}`;
	return undefined;
}

function recordOf(packument) {
	let best;
	for (const [version, manifest] of Object.entries(packument.versions ?? {})) {
		const match = RELEASE.exec(version);
		const published = Date.parse(packument.time?.[version] ?? "");
		if (!match || !(published < cutoffEnd)) continue;
		const key = match.slice(1).map(Number);
		if (!best || compareRelease(key, best.key) > 0) best = { key, version, manifest };
	}
	if (!best) return { missing: `no release published on or before ${CUTOFF}` };
	const { manifest } = best;
	const dist = manifest.dist ?? {};
	const targets =
		manifest.exports !== undefined
			? stringLeaves(manifest.exports)
			: stringLeaves([manifest.main, manifest.module, manifest.bin]);
	return {
		version: best.version,
		integrity: integrityOf(dist),
		tarball: dist.tarball,
		unpackedSize: dist.unpackedSize,
		targets,
	};
}

async function packumentRecord(name) {
	return withRetries(name, ATTEMPTS, async () => {
		const response = await fetch(REGISTRY + name.replace("/", "%2f"), {
			headers: { accept: "application/json" },
			signal: AbortSignal.timeout(180_000),
		});
		if (response.status === 404) return { missing: "not in the registry" };
		if (!response.ok) throw new Error(`registry answered ${response.status}`);
		return recordOf(await response.json());
	});
}

function eligible(name, record) {
	return (
		!record.missing &&
		!name.startsWith("@types/") &&
		Number.isInteger(record.unpackedSize) &&
		typeof record.integrity === "string" &&
		typeof record.tarball === "string" &&
		(record.targets.length === 0 ||
			record.targets.some((target) => isSourcePath(target) || path.extname(target) === ""))
	);
}

function cString(block, start, end) {
	const slice = block.subarray(start, end);
	const zero = slice.indexOf(0);
	return slice.subarray(0, zero === -1 ? slice.length : zero).toString("utf8");
}

function tarFiles(gzipped) {
	const archive = gunzipSync(gzipped);
	const files = [];
	let pending;
	for (let offset = 0; offset + 512 <= archive.length;) {
		const header = archive.subarray(offset, offset + 512);
		if (header.every((byte) => byte === 0)) break;
		const size = parseInt(cString(header, 124, 136).trim() || "0", 8);
		const type = String.fromCharCode(header[156] || 48);
		const body = archive.subarray(offset + 512, offset + 512 + size);
		const prefix = cString(header, 257, 262) === "ustar" ? cString(header, 345, 500) : "";
		const name = pending ?? (prefix ? `${prefix}/${cString(header, 0, 100)}` : cString(header, 0, 100));
		pending = undefined;
		if (type === "L") pending = cString(body, 0, body.length);
		else if (type === "x") pending = /(?:^|\n)\d+ path=([^\n]*)\n/.exec(body.toString("utf8"))?.[1];
		else if (type === "0" || type === "7") files.push(name);
		offset += 512 + Math.ceil(size / 512) * 512;
	}
	return files;
}

async function shipsSources(name, record) {
	const tarball = await withRetries(`${name} tarball`, ATTEMPTS, () =>
		pacote
			.tarball(`${name}@${record.version}`, { integrity: record.integrity, resolved: record.tarball })
			.catch((error) => {
				if (error.code === "E404") error.permanent = true;
				throw error;
			}),
	).catch((error) => {
		if (error.code === "E404") return undefined;
		throw error;
	});
	if (!tarball) return false;
	return tarFiles(tarball).some((file) => isSourcePath(file.split("/").slice(1).join("/")));
}

mkdirSync(cacheDir, { recursive: true });

const registryKey = `npm-high-impact@${listVersion} cutoff ${CUTOFF}`;
const records = readCache(registryCachePath, registryKey);
const names = [...new Set(npmHighImpact)];
const unresolved = names.filter((name) => !(name in records));
let resolved = 0;
console.error(`resolving ${unresolved.length} of ${names.length} packages against the registry`);
await mapPool(unresolved, CONCURRENCY, async (name) => {
	records[name] = await packumentRecord(name);
	if (++resolved % 500 === 0) {
		console.error(`resolved ${resolved}/${unresolved.length}`);
		writeCache(registryCachePath, registryKey, records);
	}
});
writeCache(registryCachePath, registryKey, records);

const rank = new Map(names.map((name, index) => [name, index]));
const population = names
	.filter((name) => eligible(name, records[name]))
	.sort((left, right) => records[left].unpackedSize - records[right].unpackedSize || rank.get(left) - rank.get(right));
const listings = readCache(listingCachePath, "listings");
const selected = [];
const bands = [];

for (let band = 0; band < BAND_COUNT; band++) {
	const members = population
		.slice(
			Math.floor((band * population.length) / BAND_COUNT),
			Math.floor(((band + 1) * population.length) / BAND_COUNT),
		)
		.sort((left, right) => rank.get(left) - rank.get(right));
	const accepted = [];
	for (let start = 0; start < members.length && accepted.length < BAND_SIZE;) {
		const batch = members.slice(start, start + (BAND_SIZE - accepted.length));
		start += batch.length;
		await mapPool(batch, CONCURRENCY, async (name) => {
			const key = `${name}@${records[name].version}`;
			listings[key] ??= await shipsSources(name, records[name]);
		});
		writeCache(listingCachePath, "listings", listings);
		for (const name of batch)
			if (accepted.length < BAND_SIZE && listings[`${name}@${records[name].version}`]) accepted.push(name);
	}
	const sizes = members.map((name) => records[name].unpackedSize);
	bands.push({
		band,
		population: members.length,
		minUnpackedSize: Math.min(...sizes),
		maxUnpackedSize: Math.max(...sizes),
		selected: accepted.length,
	});
	selected.push(...accepted);
	console.error(
		`band ${band}: ${accepted.length} of ${members.length}, sizes ${Math.min(...sizes)}..${Math.max(...sizes)}`,
	);
}

const packages = selected
	.sort((left, right) => (left < right ? -1 : left > right ? 1 : 0))
	.map((name) => ({
		name,
		version: records[name].version,
		integrity: records[name].integrity,
		tarball: records[name].tarball,
	}));
writeFileSync(packagesPath, stableJson(packages));
writeFileSync(
	bandsPath,
	stableJson({ listVersion, cutoff: CUTOFF, bandCount: BAND_COUNT, bandSize: BAND_SIZE, bands }),
);
console.error(`wrote ${packages.length} packages to ${path.relative(process.cwd(), packagesPath)}`);
