import { createRequire } from "node:module";
import path from "node:path";
import fs from "node:fs";

const input = JSON.parse(fs.readFileSync(0, "utf8"));
const tsconfig = path.resolve(input.tsconfig);
const projectDir = path.dirname(tsconfig);

const resolveTypescript = () => {
	for (const from of [projectDir, process.cwd()]) {
		try {
			return createRequire(path.join(from, "noop.js")).resolve("typescript");
		} catch {}
	}
	return undefined;
};
const tsPath = resolveTypescript();
if (!tsPath) {
	process.stderr.write("typescript not found from project or cwd");
	process.exit(3);
}
const ts = (await import("file://" + tsPath)).default;

const parsed = ts.getParsedCommandLineOfConfigFile(
	tsconfig,
	{},
	{
		...ts.sys,
		onUnRecoverableConfigFileDiagnostic: (d) => {
			throw new Error(ts.flattenDiagnosticMessageText(d.messageText, "\n"));
		},
	},
);
const program = ts.createProgram(parsed.fileNames, parsed.options);
const checker = program.getTypeChecker();

const TYPED_ARRAYS = new Set([
	"Int8Array",
	"Uint8Array",
	"Uint8ClampedArray",
	"Int16Array",
	"Uint16Array",
	"Int32Array",
	"Uint32Array",
	"Float32Array",
	"Float64Array",
	"BigInt64Array",
	"BigUint64Array",
]);
const rank = { array: 6, set: 5, map: 5, unknown: 4, string: 3, regexp: 2, other: 1 };
const kindOfType = (t) => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return "unknown";
	if (t.isUnion()) return t.types.map(kindOfType).reduce((a, b) => (rank[b] > rank[a] ? b : a), "other");
	if (t.flags & ts.TypeFlags.StringLike) return "string";
	if (checker.isArrayType?.(t) || checker.isTupleType?.(t)) return "array";
	const name = t.getSymbol()?.getName() ?? "";
	if (name === "Array" || name === "ReadonlyArray" || TYPED_ARRAYS.has(name)) return "array";
	if (name === "Set" || name === "ReadonlySet" || name === "WeakSet") return "set";
	if (name === "Map" || name === "ReadonlyMap" || name === "WeakMap") return "map";
	if (name === "String") return "string";
	if (name === "RegExp") return "regexp";
	if (t.isTypeParameter()) {
		const base = t.getConstraint();
		return base ? kindOfType(base) : "other";
	}
	return "other";
};
const isTuple = (t) => !!checker.isTupleType?.(t);
const isClosedObject = (t) => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive)) return false;
	if (t.isUnion() || t.isIntersection()) return t.types.every(isClosedObject);
	if (t.isTypeParameter()) {
		const base = t.getConstraint();
		return base ? isClosedObject(base) : false;
	}
	if (!(t.flags & ts.TypeFlags.Object)) return false;
	if (kindOfType(t) !== "other") return false;
	if (checker.getIndexInfosOfType(t).length > 0) return false;
	if (t.getSymbol()?.getName() === "Object") return false;
	return t.getProperties().length > 0;
};

const findNode = (sf, pos, end) => {
	let best;
	const visit = (n) => {
		if (n.getStart(sf) > pos || n.getEnd() < end) return;
		if (n.getStart(sf) === pos && n.getEnd() === end) best = n;
		n.forEachChild(visit);
	};
	visit(sf);
	return best;
};
const unwrapNode = (n) => {
	while (
		n &&
		(ts.isParenthesizedExpression(n) ||
			ts.isAsExpression(n) ||
			ts.isSatisfiesExpression(n) ||
			ts.isNonNullExpression(n) ||
			ts.isTypeAssertionExpression(n))
	)
		n = n.expression;
	return n;
};

const offsets = new Map();
const offsetsOf = (sf) => {
	const cached = offsets.get(sf.fileName);
	if (cached) return cached;
	const text = sf.text;
	const onDisk = fs.existsSync(sf.fileName) ? fs.readFileSync(sf.fileName) : Buffer.alloc(0);
	const bom =
		onDisk.length >= 3 &&
		onDisk[0] === 0xef &&
		onDisk[1] === 0xbb &&
		onDisk[2] === 0xbf &&
		text.charCodeAt(0) !== 0xfeff
			? 3
			: 0;
	const bytes = Buffer.from(text, "utf8").length;
	const utf16OfUtf8 = new Int32Array(bytes + 1);
	const utf8OfUtf16 = new Int32Array(text.length + 1);
	let byte = 0;
	let unit = 0;
	while (unit < text.length) {
		const code = text.codePointAt(unit);
		const units = code > 0xffff ? 2 : 1;
		const width = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;
		for (let k = 0; k < width; k++) utf16OfUtf8[byte + k] = unit;
		for (let k = 0; k < units; k++) utf8OfUtf16[unit + k] = byte;
		byte += width;
		unit += units;
	}
	utf16OfUtf8[byte] = unit;
	utf8OfUtf16[unit] = byte;
	const entry = {
		toUtf16: (offset) => utf16OfUtf8[Math.min(Math.max(offset - bom, 0), bytes)],
		toUtf8: (offset) => utf8OfUtf16[Math.min(Math.max(offset, 0), text.length)] + bom,
	};
	offsets.set(sf.fileName, entry);
	return entry;
};

const symbolOf = (node) => {
	let symbol = checker.getSymbolAtLocation(node);
	if (!symbol) return undefined;
	if (symbol.flags & ts.SymbolFlags.Alias) symbol = checker.getAliasedSymbol(symbol);
	return symbol;
};

const files = new Map();
const answers = input.queries.map((q) => {
	const file = path.resolve(q.file);
	const sf = files.get(file) ?? program.getSourceFile(file);
	if (!sf) return null;
	files.set(file, sf);
	const offset = offsetsOf(sf);
	const n = findNode(sf, offset.toUtf16(q.pos), offset.toUtf16(q.end));
	if (!n) return null;
	if (q.query === "callee") {
		const node = unwrapNode(n);
		if (!node || !ts.isPropertyAccessExpression(node)) return null;
		const declaration = symbolOf(node.name)?.declarations?.[0];
		if (!declaration) return null;
		const declarationFile = declaration.getSourceFile();
		const declarationOffset = offsetsOf(declarationFile);
		return {
			query: "callee",
			file: declarationFile.fileName,
			start: declarationOffset.toUtf8(declaration.getStart(declarationFile)),
			end: declarationOffset.toUtf8(declaration.getEnd()),
		};
	}
	const t = checker.getTypeAtLocation(unwrapNode(n) ?? n);
	return {
		query: "type",
		kind: kindOfType(t),
		tuple: isTuple(t) || (t.isUnion() && t.types.length > 0 && t.types.every(isTuple)),
		closed: isClosedObject(t),
	};
});
process.stdout.write(JSON.stringify({ typescript: ts.version, from: tsPath, answers }));
