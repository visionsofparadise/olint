import { createRequire } from "node:module";
import path from "node:path";
import fs from "node:fs";

const PROTOCOL_VERSION = 2;
const MAXIMUM_CANDIDATE_SYMBOLS = 1024;

const input = JSON.parse(fs.readFileSync(0, "utf8"));
if (input.version !== PROTOCOL_VERSION) {
	process.stderr.write(`protocol version ${JSON.stringify(input.version)} where ${PROTOCOL_VERSION} is supported`);
	process.exit(2);
}
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

const programsOf = () => {
	const programs = [];
	const pending = [tsconfig];
	const visited = new Set();
	while (pending.length) {
		const config = fs.realpathSync(pending.pop());
		const key = ts.sys.useCaseSensitiveFileNames ? config : config.toLowerCase();
		if (visited.has(key)) continue;
		if (visited.size >= 1024) throw new Error("project reference graph exceeds 1024 configurations");
		visited.add(key);
		const parsed = ts.getParsedCommandLineOfConfigFile(
			config,
			{},
			{
				...ts.sys,
				onUnRecoverableConfigFileDiagnostic: (d) => {
					throw new Error(ts.flattenDiagnosticMessageText(d.messageText, "\n"));
				},
			},
		);
		programs.push(
			ts.createProgram({
				rootNames: parsed.fileNames,
				options: parsed.options,
				projectReferences: parsed.projectReferences,
			}),
		);
		for (const reference of [...(parsed.projectReferences ?? [])].reverse()) {
			pending.push(ts.resolveProjectReferencePath(reference));
		}
	}
	return programs;
};

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
const kindOfType = (checker, t) => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return "unknown";
	if (t.isUnion())
		return t.types.map((type) => kindOfType(checker, type)).reduce((a, b) => (rank[b] > rank[a] ? b : a), "other");
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
		return base ? kindOfType(checker, base) : "other";
	}
	return "other";
};
const isTuple = (checker, t) => !!checker.isTupleType?.(t);
const isStructuralObject = (checker, t) => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive)) return false;
	if (t.isUnion() || t.isIntersection()) return t.types.every((type) => isStructuralObject(checker, type));
	if (t.isTypeParameter()) {
		const base = t.getConstraint();
		return base ? isStructuralObject(checker, base) : false;
	}
	if (!(t.flags & ts.TypeFlags.Object)) return false;
	if (kindOfType(checker, t) !== "other") return false;
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

const aliasedOf = (checker, symbol) =>
	symbol.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;

const isExecutable = (node) =>
	!!node.body &&
	(ts.isFunctionDeclaration(node) ||
		ts.isMethodDeclaration(node) ||
		ts.isConstructorDeclaration(node) ||
		ts.isFunctionExpression(node) ||
		ts.isArrowFunction(node));

const implementationsOf = (checker, declaration) => {
	if (declaration.body) return [declaration];
	const own = declaration.name && checker.getSymbolAtLocation(declaration.name);
	return (own?.declarations ?? []).filter((other) => other.kind === declaration.kind && isExecutable(other));
};

const candidatesOf = (checker, symbols) => {
	const targets = new Set();
	const seen = new Set();
	const pending = [...symbols];
	const follow = (symbol) => symbol && pending.push(symbol);
	while (pending.length && seen.size < MAXIMUM_CANDIDATE_SYMBOLS) {
		const symbol = aliasedOf(checker, pending.pop());
		if (seen.has(symbol)) continue;
		seen.add(symbol);
		for (const declaration of symbol.declarations ?? []) {
			if (ts.isClassLike(declaration)) {
				for (const member of declaration.members)
					if (isExecutable(member) && ts.isConstructorDeclaration(member)) targets.add(member);
			} else if (
				ts.isFunctionDeclaration(declaration) ||
				ts.isMethodDeclaration(declaration) ||
				ts.isFunctionExpression(declaration) ||
				ts.isArrowFunction(declaration)
			) {
				for (const implementation of implementationsOf(checker, declaration)) targets.add(implementation);
			} else if (ts.isShorthandPropertyAssignment(declaration)) {
				follow(checker.getShorthandAssignmentValueSymbol(declaration));
			} else if (
				ts.isVariableDeclaration(declaration) ||
				ts.isPropertyAssignment(declaration) ||
				ts.isPropertyDeclaration(declaration)
			) {
				const value = unwrapNode(declaration.initializer);
				if (value && (ts.isFunctionExpression(value) || ts.isArrowFunction(value))) targets.add(value);
				else if (value && ts.isIdentifier(value)) follow(checker.getSymbolAtLocation(value));
				else if (value && ts.isPropertyAccessExpression(value)) follow(checker.getSymbolAtLocation(value.name));
			}
		}
	}
	return [...targets];
};

const signatureSymbolsOf = (checker, callee) => {
	let call = callee;
	while (call.parent && unwrapNode(call.parent) === callee) call = call.parent;
	call = call.parent;
	if (!call || !ts.isCallOrNewExpression(call) || unwrapNode(call.expression) !== callee) return [];
	const declaration = checker.getResolvedSignature(call)?.declaration;
	const own = declaration && declaration.name && checker.getSymbolAtLocation(declaration.name);
	return own ? [own] : [];
};

const calleeAnswerOf = (checker, node) => {
	const symbol = checker.getSymbolAtLocation(node.name);
	const spans = new Map();
	for (const target of candidatesOf(checker, symbol ? [symbol] : signatureSymbolsOf(checker, node))) {
		const file = target.getSourceFile();
		const offset = offsetsOf(file);
		const span = {
			file: file.fileName,
			start: offset.toUtf8(target.getStart(file)),
			end: offset.toUtf8(target.getEnd()),
		};
		spans.set(`${span.file}\u0000${span.start}\u0000${span.end}`, span);
	}
	return { query: "callee", targets: [...spans.values()], open: true };
};

const answerOf = (program, q) => {
	const checker = program.getTypeChecker();
	const file = path.resolve(q.file);
	const sf = program.getSourceFile(file);
	if (!sf) return null;
	const offset = offsetsOf(sf);
	const n = findNode(sf, offset.toUtf16(q.pos), offset.toUtf16(q.end));
	if (!n) return null;
	if (q.query === "callee") {
		const node = unwrapNode(n);
		if (!node || !ts.isPropertyAccessExpression(node)) return null;
		return calleeAnswerOf(checker, node);
	}
	const t = checker.getTypeAtLocation(unwrapNode(n) ?? n);
	return {
		query: "type",
		kind: kindOfType(checker, t),
		tuple:
			isTuple(checker, t) || (t.isUnion() && t.types.length > 0 && t.types.every((type) => isTuple(checker, type))),
		structural: isStructuralObject(checker, t),
	};
};
const answersOf = (queries) => {
	const programs = programsOf();
	return queries.map((query) => {
		const applicable = programs.filter((program) => program.getSourceFile(path.resolve(query.file)));
		if (!applicable.length) return null;
		const answers = applicable.map((program) => answerOf(program, query));
		const first = JSON.stringify(answers[0]);
		return answers.every((answer) => JSON.stringify(answer) === first) ? answers[0] : null;
	});
};
process.stdout.write(
	JSON.stringify({
		version: PROTOCOL_VERSION,
		typescript: ts.version,
		from: tsPath,
		answers: input.queries.length ? answersOf(input.queries) : [],
	}),
);
