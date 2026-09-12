// Type oracle: answers batched type questions using the project's own TypeScript.
// stdin:  { tsconfig: string, queries: [{ file: string, pos: number, end: number }] }
// stdout: { typescript: string, from: string, answers: [{ kind, tuple, closed } | null] }
import { createRequire } from "node:module";
import path from "node:path";
import fs from "node:fs";

const input = JSON.parse(fs.readFileSync(0, "utf8"));
const tsconfig = path.resolve(input.tsconfig);
const projectDir = path.dirname(tsconfig);

const resolveTypescript = () => {
	for (const from of [projectDir, process.cwd(), path.dirname(new URL(import.meta.url).pathname)]) {
		try {
			return createRequire(path.join(from, "noop.js")).resolve("typescript");
		} catch {}
	}
	throw new Error("typescript not found from project, cwd or oracle location");
};
const tsPath = resolveTypescript();
const ts = (await import("file://" + tsPath)).default;

const parsed = ts.getParsedCommandLineOfConfigFile(tsconfig, {}, {
	...ts.sys,
	onUnRecoverableConfigFileDiagnostic: (d) => {
		throw new Error(ts.flattenDiagnosticMessageText(d.messageText, "\n"));
	},
});
const program = ts.createProgram(parsed.fileNames, parsed.options);
const checker = program.getTypeChecker();

const TYPED_ARRAYS = new Set(["Int8Array", "Uint8Array", "Uint8ClampedArray", "Int16Array", "Uint16Array", "Int32Array", "Uint32Array", "Float32Array", "Float64Array", "BigInt64Array", "BigUint64Array"]);
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
const closedObject = (t) => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive)) return false;
	if (t.isUnion() || t.isIntersection()) return t.types.every(closedObject);
	if (t.isTypeParameter()) {
		const base = t.getConstraint();
		return base ? closedObject(base) : false;
	}
	if (!(t.flags & ts.TypeFlags.Object)) return false;
	if (kindOfType(t) !== "other") return false;
	if (checker.getIndexInfosOfType(t).length > 0) return false;
	if (t.getSymbol()?.getName() === "Object") return false;
	return t.getProperties().length > 0;
};

const nodeAt = (sf, pos, end) => {
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
	while (n && (ts.isParenthesizedExpression(n) || ts.isAsExpression(n) || ts.isSatisfiesExpression(n) || ts.isNonNullExpression(n) || ts.isTypeAssertionExpression(n))) n = n.expression;
	return n;
};

const files = new Map();
const answers = input.queries.map((q) => {
	const file = path.resolve(q.file);
	const sf = files.get(file) ?? program.getSourceFile(file);
	if (!sf) return null;
	files.set(file, sf);
	const n = nodeAt(sf, q.pos, q.end);
	if (!n) return null;
	const t = checker.getTypeAtLocation(unwrapNode(n) ?? n);
	return { kind: kindOfType(t), tuple: isTuple(t) || (t.isUnion() && t.types.length > 0 && t.types.every(isTuple)), closed: closedObject(t) };
});
process.stdout.write(JSON.stringify({ typescript: ts.version, from: tsPath, answers }));
