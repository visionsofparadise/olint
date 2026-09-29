import path from "node:path";
import { fileURLToPath } from "node:url";

export const corpusDir = path.dirname(fileURLToPath(import.meta.url));
export const cacheDir = path.join(corpusDir, ".cache");
export const packagesPath = path.join(cacheDir, "packages.json");
export const extractedDir = path.join(cacheDir, "packages");

export const SOURCE_EXTENSIONS = [".js", ".mjs", ".cjs", ".ts", ".tsx"];

const DECLARATION = /\.d\.[cm]?ts$/;

export function isSourcePath(file) {
	const normalized = file.replaceAll("\\", "/");
	return (
		!normalized.split("/").includes("node_modules") &&
		!DECLARATION.test(normalized) &&
		SOURCE_EXTENSIONS.some((extension) => normalized.endsWith(extension))
	);
}

export function stableJson(value) {
	return JSON.stringify(value, null, "\t") + "\n";
}

export function sleep(milliseconds) {
	return new Promise((resolve) => setTimeout(resolve, milliseconds));
}

export async function withRetries(label, attempts, task) {
	for (let attempt = 1; ; attempt++) {
		try {
			return await task();
		} catch (error) {
			if (attempt >= attempts || error.permanent) throw error;
			console.error(`${label}: attempt ${attempt} failed (${error.message}); retrying`);
			await sleep(500 * 2 ** attempt);
		}
	}
}

export async function mapPool(items, concurrency, task) {
	const results = new Array(items.length);
	let next = 0;
	const worker = async () => {
		while (next < items.length) {
			const index = next++;
			results[index] = await task(items[index], index);
		}
	};
	await Promise.all(Array.from({ length: Math.min(concurrency, items.length) }, worker));
	return results;
}

export function packageDir(name, version) {
	return path.join(extractedDir, `${name}@${version}`);
}

export function stringLeaves(value, found = []) {
	if (typeof value === "string") found.push(value);
	else if (Array.isArray(value)) for (const item of value) stringLeaves(item, found);
	else if (value && typeof value === "object") for (const item of Object.values(value)) stringLeaves(item, found);
	return found;
}
