import ts from "typescript";
import path from "node:path";
import fs from "node:fs";
import childProcess from "node:child_process";

type Cost = { n: number; log: number };
type Factor = { label: string; file: string; line: number; cost: Cost; inner?: Factor[] };
type Part = { cost: Cost; chain: Factor[] };
type Result = { main: Part; fnExit: Part; loopExit: Part };

const ONE: Cost = { n: 0, log: 0 };
const N: Cost = { n: 1, log: 0 };
const LOG: Cost = { n: 0, log: 1 };
const NLOGN: Cost = { n: 1, log: 1 };
const isOne = (c: Cost) => c.n === 0 && c.log === 0;
const mul = (a: Cost, b: Cost): Cost => ({ n: a.n + b.n, log: a.log + b.log });
const gt = (a: Cost, b: Cost) => (a.n !== b.n ? a.n > b.n : a.log > b.log);
const fmt = (c: Cost) => {
	if (isOne(c)) return "O(1)";
	const n = c.n === 0 ? "" : c.n === 1 ? "N" : `N^${c.n}`;
	const l = c.log === 0 ? "" : c.log === 1 ? "log N" : `log^${c.log} N`;
	return `O(${[n, l].filter(Boolean).join(" ")})`;
};
const none = (): Part => ({ cost: ONE, chain: [] });
const maxPart = (a: Part, b: Part): Part => (gt(b.cost, a.cost) ? b : a);
const empty = (): Result => ({ main: none(), fnExit: none(), loopExit: none() });
const merge = (a: Result, b: Result): Result => ({ main: maxPart(a.main, b.main), fnExit: maxPart(a.fnExit, b.fnExit), loopExit: maxPart(a.loopExit, b.loopExit) });
const ofPart = (p: Part): Result => ({ main: p, fnExit: none(), loopExit: none() });
const total = (r: Result): Part => maxPart(maxPart(r.main, r.fnExit), r.loopExit);

const args = process.argv.slice(2);
const configPath = path.resolve(args[0]);
const minN = Number(args.find((a) => a.startsWith("--min="))?.slice(6) ?? "2");
const STRINGS_LINEAR = !args.includes("--strings-constant");
const CALLBACKS = !args.includes("--no-callbacks");

const parsed = ts.getParsedCommandLineOfConfigFile(configPath, {}, {
	...ts.sys,
	onUnRecoverableConfigFileDiagnostic: (d) => {
		throw new Error(ts.flattenDiagnosticMessageText(d.messageText, "\n"));
	},
});
if (!parsed) throw new Error("no config");
const program = ts.createProgram(parsed.fileNames, parsed.options);
const checker = program.getTypeChecker();
const root = path.dirname(configPath);
const rel = (f: string) => path.relative(root, f).replace(/\\/g, "/");
const isTestPath = (f: string) => /\.(test|spec|bench|benchmark|stories)\.[cm]?[jt]sx?$/.test(f) || /(^|\/)(tests?|__tests__|fixtures|scripts|mocks?)\//.test(rel(f));
const isProjectFile = (sf: ts.SourceFile) => !sf.isDeclarationFile && !sf.fileName.includes("/node_modules/") && !program.isSourceFileFromExternalLibrary(sf);

type Fn = ts.SignatureDeclaration & { body?: ts.Node };
const isFn = (n: ts.Node): n is Fn =>
	ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) || ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n);

const loc = (n: ts.Node) => {
	const sf = n.getSourceFile();
	return { file: rel(sf.fileName), line: sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1 };
};

const nameOf = (fn: ts.Node): string => {
	const owner = (n: ts.Node) => {
		const cls = n.parent && (ts.isClassDeclaration(n.parent) || ts.isClassExpression(n.parent)) ? n.parent.name?.text ?? "<class>" : undefined;
		return cls ? `${cls}.` : "";
	};
	if (ts.isFunctionDeclaration(fn)) return fn.name?.text ?? "<default>";
	if (ts.isMethodDeclaration(fn) || ts.isGetAccessorDeclaration(fn) || ts.isSetAccessorDeclaration(fn)) return owner(fn) + fn.name.getText();
	if (ts.isConstructorDeclaration(fn)) return owner(fn) + "constructor";
	const p = fn.parent;
	if (ts.isVariableDeclaration(p) || ts.isPropertyAssignment(p) || ts.isPropertyDeclaration(p)) return (ts.isPropertyDeclaration(p) ? owner(p) : "") + p.name.getText();
	if (ts.isFunctionExpression(fn) && fn.name) return fn.name.text;
	if (ts.isCallExpression(p) || ts.isNewExpression(p)) return "<callback>";
	if (ts.isReturnStatement(p)) return "<returned fn>";
	return "<anonymous>";
};

const ARRAY_LINEAR = new Set(["includes", "indexOf", "lastIndexOf", "find", "findIndex", "findLast", "findLastIndex", "some", "every", "filter", "map", "forEach", "reduce", "reduceRight", "flat", "flatMap", "concat", "slice", "splice", "shift", "unshift", "join", "reverse", "fill", "copyWithin", "toReversed", "toSpliced", "with", "set"]);
const ARRAY_NLOGN = new Set(["sort", "toSorted"]);
const CALLBACK_METHODS = new Set(["forEach", "map", "filter", "reduce", "reduceRight", "some", "every", "find", "findIndex", "findLast", "findLastIndex", "flatMap", "sort", "toSorted"]);
const SET_LINEAR = new Set(["forEach", "union", "intersection", "difference", "symmetricDifference", "isSubsetOf", "isSupersetOf", "isDisjointFrom"]);
const MAP_LINEAR = new Set(["forEach"]);
const STRING_LINEAR = new Set(["includes", "indexOf", "lastIndexOf", "split", "replace", "replaceAll", "match", "matchAll", "search", "slice", "substring", "substr", "repeat", "padStart", "padEnd", "trim", "trimStart", "trimEnd", "toLowerCase", "toUpperCase", "toLocaleLowerCase", "toLocaleUpperCase", "normalize", "localeCompare", "startsWith", "endsWith", "concat", "codePointAt"]);
const REGEXP_LINEAR = new Set(["test", "exec"]);
const GLOBAL_LINEAR: Record<string, Set<string>> = {
	Array: new Set(["from", "of"]),
	Object: new Set(["keys", "values", "entries", "assign", "fromEntries", "freeze", "groupBy"]),
	JSON: new Set(["parse", "stringify"]),
	Buffer: new Set(["from", "concat", "alloc", "allocUnsafe", "compare"]),
	Map: new Set(["groupBy"]),
};
const OBJECT_KEYED = new Set(["keys", "values", "entries", "freeze", "assign"]);
const METHOD_MATTERS = new Set<string>([...ARRAY_LINEAR, ...ARRAY_NLOGN, ...SET_LINEAR, ...MAP_LINEAR, ...STRING_LINEAR, ...REGEXP_LINEAR]);
const GLOBAL_FUNCTIONS_LINEAR = new Set(["structuredClone"]);
const LINEAR_CONSTRUCTORS = new Set(["Set", "Map", "WeakSet", "WeakMap", "Array", "Int8Array", "Uint8Array", "Uint8ClampedArray", "Int16Array", "Uint16Array", "Int32Array", "Uint32Array", "Float32Array", "Float64Array", "BigInt64Array", "BigUint64Array", "ArrayBuffer", "SharedArrayBuffer", "DataView"]);
const TYPED_ARRAYS = new Set(["Int8Array", "Uint8Array", "Uint8ClampedArray", "Int16Array", "Uint16Array", "Int32Array", "Uint32Array", "Float32Array", "Float64Array", "BigInt64Array", "BigUint64Array"]);

type Kind = "array" | "set" | "map" | "string" | "regexp" | "other" | "unknown";
const rank: Record<Kind, number> = { array: 6, set: 5, map: 5, unknown: 4, string: 3, regexp: 2, other: 1 };
const kindOfType = (t: ts.Type): Kind => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return "unknown";
	if (t.isUnion()) return t.types.map(kindOfType).reduce((a, b) => (rank[b] > rank[a] ? b : a), "other" as Kind);
	if (t.flags & ts.TypeFlags.StringLike) return "string";
	const c = checker as ts.TypeChecker & { isArrayType?: (t: ts.Type) => boolean; isTupleType?: (t: ts.Type) => boolean };
	if (c.isArrayType?.(t) || c.isTupleType?.(t)) return "array";
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
const isTuple = (t: ts.Type) => !!(checker as ts.TypeChecker & { isTupleType?: (t: ts.Type) => boolean }).isTupleType?.(t);
const closedObject = (t: ts.Type): boolean => {
	if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive)) return false;
	if (t.isUnion() || t.isIntersection()) return t.types.every(closedObject);
	if (t.isTypeParameter()) {
		const base = t.getConstraint();
		return base ? closedObject(base) : false;
	}
	if (!(t.flags & ts.TypeFlags.Object)) return false;
	if (kindOfType(t) !== "other") return false;
	if (checker.getIndexInfosOfType(t).length > 0) return false;
	const name = t.getSymbol()?.getName();
	if (name === "Object") return false;
	return t.getProperties().length > 0;
};

// ---- syntactic types: what a checker-free port can know ----
const TYPES: "checker" | "syntactic" | "oracle" = args.includes("--syntactic-types") ? "syntactic" : ((args.find((a) => a.startsWith("--types="))?.slice(8) as "checker" | "syntactic" | "oracle" | undefined) ?? "checker");
const SYNTACTIC = TYPES === "syntactic";
type OracleAnswer = { kind: Kind; tuple: boolean; closed: boolean };
const oracleAnswers = new Map<string, OracleAnswer | null>();
let oracleInfo = "";
const oracleKey = (e: ts.Node) => `${e.getSourceFile().fileName}:${e.getStart()}:${e.getEnd()}`;
const askOracle = (nodes: ts.Node[]) => {
	const queries = nodes.map((n) => ({ file: n.getSourceFile().fileName, pos: n.getStart(), end: n.getEnd() }));
	const script = path.join(path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1")), "types-oracle.mjs");
	const res = childProcess.spawnSync(process.execPath, [script], { input: JSON.stringify({ tsconfig: configPath, queries }), encoding: "utf8", maxBuffer: 1 << 28, cwd: root });
	if (res.status !== 0) throw new Error(`types oracle failed: ${res.stderr}`);
	const out = JSON.parse(res.stdout) as { typescript: string; from: string; answers: (OracleAnswer | null)[] };
	oracleInfo = `typescript ${out.typescript} at ${out.from}`;
	nodes.forEach((n, i) => oracleAnswers.set(oracleKey(n), out.answers[i]));
};
let oraclePass: 1 | 2 = 2;
const needed = new Map<string, ts.Node>();
const need = (e: ts.Node) => needed.set(oracleKey(e), e);
const fromOracle = (e: ts.Expression): OracleAnswer | undefined => {
	const a = oracleAnswers.get(oracleKey(e));
	if (a === undefined) count("oracle: miss");
	return a ?? undefined;
};
type Syn = { kind: Kind; tuple: boolean; closed: boolean };
const SYN_UNKNOWN: Syn = { kind: "unknown", tuple: false, closed: false };
const syn = (kind: Kind, tuple = false, closed = false): Syn => ({ kind, tuple, closed });
type Container = ts.TypeLiteralNode | ts.InterfaceDeclaration | ts.ClassLikeDeclaration | ts.ObjectLiteralExpression;
const KIND_OF_NAME: Record<string, Kind> = { Array: "array", ReadonlyArray: "array", Set: "set", ReadonlySet: "set", WeakSet: "set", Map: "map", ReadonlyMap: "map", WeakMap: "map", String: "string", RegExp: "regexp" };
const joinSyn = (parts: Syn[], closedAll: boolean): Syn => {
	if (parts.length === 0) return SYN_UNKNOWN;
	const kind = parts.map((p) => p.kind).reduce((a, b) => (rank[b] > rank[a] ? b : a), "other" as Kind);
	return { kind, tuple: parts.every((p) => p.tuple), closed: closedAll ? parts.every((p) => p.closed) : parts.some((p) => p.closed) && parts.every((p) => p.closed || p.kind === "unknown") };
};
const typeNameText = (n: ts.EntityName): string => (ts.isIdentifier(n) ? n.text : n.right.text);
const containerOfTypeNode = (t: ts.TypeNode | undefined, depth = 0): Container | undefined => {
	if (!t || depth > 8) return undefined;
	if (ts.isParenthesizedTypeNode(t)) return containerOfTypeNode(t.type, depth + 1);
	if (ts.isTypeLiteralNode(t)) return t;
	if (ts.isTypeReferenceNode(t)) {
		const name = typeNameText(t.typeName);
		if ((name === "Readonly" || name === "Required" || name === "Partial" || name === "NonNullable") && t.typeArguments?.[0]) return containerOfTypeNode(t.typeArguments[0], depth + 1);
		const d = declOf(t.typeName);
		if (d && ts.isTypeAliasDeclaration(d)) return containerOfTypeNode(d.type, depth + 1);
		if (d && (ts.isInterfaceDeclaration(d) || ts.isClassDeclaration(d))) return d;
	}
	return undefined;
};
const closedContainer = (c: Container, depth = 0): boolean => {
	if (depth > 8) return false;
	if (ts.isObjectLiteralExpression(c)) return c.properties.length > 0 && c.properties.every((p) => !ts.isSpreadAssignment(p) || synOfExpr(p.expression, depth + 1).closed);
	if (c.members.some((m) => ts.isIndexSignatureDeclaration(m))) return false;
	if (ts.isTypeLiteralNode(c)) return c.members.length > 0;
	for (const h of c.heritageClauses ?? []) {
		for (const e of h.types) {
			const d = declOf(e.expression);
			if (!d) return false;
			if (ts.isInterfaceDeclaration(d) || ts.isClassDeclaration(d)) {
				if (!closedContainer(d, depth + 1)) return false;
			} else if (ts.isTypeAliasDeclaration(d)) {
				if (!synOfTypeNode(d.type, depth + 1).closed) return false;
			} else return false;
		}
	}
	return c.members.length > 0 || (c.heritageClauses?.length ?? 0) > 0;
};
const synOfTypeNode = (t: ts.TypeNode | undefined, depth = 0): Syn => {
	if (!t || depth > 8) return SYN_UNKNOWN;
	if (ts.isParenthesizedTypeNode(t)) return synOfTypeNode(t.type, depth + 1);
	if (ts.isTypeOperatorNode(t)) return synOfTypeNode(t.type, depth + 1);
	if (ts.isTupleTypeNode(t)) return syn("array", true);
	if (ts.isArrayTypeNode(t)) return syn("array");
	if (t.kind === ts.SyntaxKind.StringKeyword || ts.isTemplateLiteralTypeNode(t) || (ts.isLiteralTypeNode(t) && (ts.isStringLiteral(t.literal) || ts.isNoSubstitutionTemplateLiteral(t.literal)))) return syn("string");
	if (t.kind === ts.SyntaxKind.AnyKeyword || t.kind === ts.SyntaxKind.UnknownKeyword) return SYN_UNKNOWN;
	if (t.kind === ts.SyntaxKind.ObjectKeyword) return syn("other");
	if (ts.isTypeLiteralNode(t)) return syn("other", false, closedContainer(t, depth + 1));
	if (ts.isUnionTypeNode(t)) return joinSyn(t.types.map((x) => synOfTypeNode(x, depth + 1)), true);
	if (ts.isIntersectionTypeNode(t)) return joinSyn(t.types.map((x) => synOfTypeNode(x, depth + 1)), false);
	if (ts.isTypeReferenceNode(t)) {
		const name = typeNameText(t.typeName);
		if (KIND_OF_NAME[name]) return syn(KIND_OF_NAME[name]);
		if (TYPED_ARRAYS.has(name)) return syn("array");
		if ((name === "Readonly" || name === "Required" || name === "Partial" || name === "NonNullable") && t.typeArguments?.[0]) return synOfTypeNode(t.typeArguments[0], depth + 1);
		if ((name === "Pick" || name === "Omit") && t.typeArguments?.[0]) return syn("other", false, synOfTypeNode(t.typeArguments[0], depth + 1).closed);
		const d = declOf(t.typeName);
		if (!d) return SYN_UNKNOWN;
		if (ts.isTypeAliasDeclaration(d)) return synOfTypeNode(d.type, depth + 1);
		if (ts.isInterfaceDeclaration(d) || ts.isClassDeclaration(d)) return syn("other", false, closedContainer(d, depth + 1));
		if (ts.isEnumDeclaration(d)) return syn("other", false, true);
		if (ts.isTypeParameterDeclaration(d)) return d.constraint ? synOfTypeNode(d.constraint, depth + 1) : SYN_UNKNOWN;
		return SYN_UNKNOWN;
	}
	return syn("other");
};
const memberOf = (c: Container | undefined, name: string): ts.Node | undefined => {
	if (!c) return undefined;
	if (ts.isObjectLiteralExpression(c)) return c.properties.find((p) => p.name && ts.isIdentifier(p.name) && p.name.text === name);
	return c.members.find((m) => m.name && ts.isIdentifier(m.name) && m.name.text === name);
};
const synOfMember = (m: ts.Node | undefined, depth: number): Syn => {
	if (!m) return SYN_UNKNOWN;
	if (ts.isPropertyAssignment(m)) return synOfExpr(m.initializer, depth + 1);
	if (ts.isShorthandPropertyAssignment(m)) return synOfExpr(m.name, depth + 1);
	if ((ts.isPropertySignature(m) || ts.isPropertyDeclaration(m)) && m.type) return synOfTypeNode(m.type, depth + 1);
	if (ts.isPropertyDeclaration(m) && m.initializer) return synOfExpr(m.initializer, depth + 1);
	if (ts.isGetAccessorDeclaration(m) && m.type) return synOfTypeNode(m.type, depth + 1);
	return SYN_UNKNOWN;
};
const returnSynOfMember = (m: ts.Node | undefined, depth: number): Syn => {
	if (!m) return SYN_UNKNOWN;
	if ((ts.isMethodSignature(m) || ts.isMethodDeclaration(m)) && m.type) return synOfTypeNode(m.type, depth + 1);
	if ((ts.isPropertySignature(m) || ts.isPropertyDeclaration(m)) && m.type && ts.isFunctionTypeNode(m.type)) return synOfTypeNode(m.type.type, depth + 1);
	if (ts.isPropertyDeclaration(m) && m.initializer && isFn(m.initializer) && m.initializer.type) return synOfTypeNode(m.initializer.type, depth + 1);
	if (ts.isPropertyAssignment(m) && isFn(m.initializer) && m.initializer.type) return synOfTypeNode(m.initializer.type, depth + 1);
	return SYN_UNKNOWN;
};
const containerOfExpr = (e: ts.Expression, depth: number): Container | undefined => {
	e = unwrap(e);
	if (e.kind === ts.SyntaxKind.ThisKeyword) {
		for (let p = e.parent; p; p = p.parent) if (ts.isClassLike(p)) return p;
		return undefined;
	}
	if (ts.isObjectLiteralExpression(e)) return e;
	if (ts.isNewExpression(e) && ts.isIdentifier(e.expression)) {
		const d = declOf(e.expression);
		return d && ts.isClassDeclaration(d) ? d : undefined;
	}
	if (ts.isIdentifier(e)) {
		const d = declOf(e);
		if (!d) return undefined;
		if ((ts.isVariableDeclaration(d) || ts.isParameter(d) || ts.isPropertyDeclaration(d)) && d.type) return containerOfTypeNode(d.type);
		if ((ts.isVariableDeclaration(d) || ts.isParameter(d) || ts.isPropertyDeclaration(d)) && d.initializer) return containerOfExpr(d.initializer, depth + 1);
		if (ts.isPropertySignature(d) && d.type) return containerOfTypeNode(d.type);
		return undefined;
	}
	if (ts.isPropertyAccessExpression(e)) {
		const m = memberOf(containerOfExpr(e.expression, depth + 1), e.name.text);
		if (!m) return undefined;
		if (ts.isPropertyAssignment(m)) return containerOfExpr(m.initializer, depth + 1);
		if ((ts.isPropertySignature(m) || ts.isPropertyDeclaration(m)) && m.type) return containerOfTypeNode(m.type);
		if (ts.isPropertyDeclaration(m) && m.initializer) return containerOfExpr(m.initializer, depth + 1);
		return undefined;
	}
	if (ts.isCallExpression(e)) {
		const callee = unwrap(e.expression);
		if (ts.isIdentifier(callee)) {
			const d = declOf(callee);
			const fn = d && isFn(d) ? d : d && ts.isVariableDeclaration(d) && d.initializer && isFn(d.initializer) ? d.initializer : undefined;
			return fn?.type ? containerOfTypeNode(fn.type) : undefined;
		}
		if (ts.isPropertyAccessExpression(callee)) {
			const m = memberOf(containerOfExpr(callee.expression, depth + 1), callee.name.text);
			if (m && (ts.isMethodSignature(m) || ts.isMethodDeclaration(m)) && m.type) return containerOfTypeNode(m.type);
		}
	}
	return undefined;
};
const STRING_TO_ARRAY = new Set(["split", "match"]);
const ARRAY_TO_ARRAY = new Set(["map", "filter", "slice", "concat", "flat", "flatMap", "sort", "toSorted", "reverse", "toReversed", "with", "toSpliced", "splice", "fill"]);
const synOfExpr = (e: ts.Expression, depth = 0): Syn => {
	if (depth > 8) return SYN_UNKNOWN;
	if ((ts.isAsExpression(e) || ts.isSatisfiesExpression(e)) && !(ts.isTypeReferenceNode(e.type) && typeNameText(e.type.typeName) === "const")) return synOfTypeNode(e.type, depth + 1);
	e = unwrap(e);
	if (ts.isArrayLiteralExpression(e)) return syn("array", !e.elements.some(ts.isSpreadElement));
	if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e) || ts.isTemplateExpression(e)) return syn("string");
	if (ts.isRegularExpressionLiteral(e)) return syn("regexp");
	if (ts.isObjectLiteralExpression(e)) return syn("other", false, closedContainer(e, depth + 1));
	if (ts.isNewExpression(e) && ts.isIdentifier(e.expression)) {
		const n = e.expression.text;
		if (KIND_OF_NAME[n]) return syn(KIND_OF_NAME[n]);
		if (TYPED_ARRAYS.has(n)) return syn("array");
		const d = declOf(e.expression);
		return d && ts.isClassDeclaration(d) ? syn("other", false, closedContainer(d, depth + 1)) : syn("other");
	}
	if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.PlusToken) {
		const [l, r] = [synOfExpr(e.left, depth + 1), synOfExpr(e.right, depth + 1)];
		return l.kind === "string" || r.kind === "string" ? syn("string") : SYN_UNKNOWN;
	}
	if (ts.isConditionalExpression(e)) return joinSyn([synOfExpr(e.whenTrue, depth + 1), synOfExpr(e.whenFalse, depth + 1)], true);
	if (ts.isBinaryExpression(e) && (e.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken || e.operatorToken.kind === ts.SyntaxKind.BarBarToken)) return joinSyn([synOfExpr(e.left, depth + 1), synOfExpr(e.right, depth + 1)], true);
	if (ts.isCallExpression(e)) {
		const callee = unwrap(e.expression);
		if (ts.isPropertyAccessExpression(callee)) {
			const m = callee.name.text;
			const recv = unwrap(callee.expression);
			if (ts.isIdentifier(recv) && (recv.text === "Object" || recv.text === "Array") && (m === "keys" || m === "values" || m === "entries" || m === "from" || m === "of")) return syn("array");
			if (ts.isIdentifier(recv) && recv.text === "JSON" && m === "stringify") return syn("string");
			const r = synOfExpr(recv, depth + 1);
			if (r.kind === "string" && STRING_TO_ARRAY.has(m)) return syn("array");
			if (r.kind === "string" && STRING_LINEAR.has(m) && m !== "split" && m !== "match" && m !== "matchAll" && m !== "search" && m !== "indexOf" && m !== "lastIndexOf" && m !== "includes" && m !== "startsWith" && m !== "endsWith" && m !== "localeCompare" && m !== "codePointAt") return syn("string");
			if (r.kind === "array" && ARRAY_TO_ARRAY.has(m)) return syn("array");
			if (m === "join" || m === "toString" || m === "toLowerCase" || m === "toUpperCase" || m === "trim") return syn("string");
			return returnSynOfMember(memberOf(containerOfExpr(recv, depth + 1), m), depth + 1);
		}
		if (ts.isIdentifier(callee)) {
			const d = declOf(callee);
			const fn = d && isFn(d) ? d : d && ts.isVariableDeclaration(d) && d.initializer && isFn(d.initializer) ? d.initializer : undefined;
			return fn?.type ? synOfTypeNode(fn.type, depth + 1) : SYN_UNKNOWN;
		}
		return SYN_UNKNOWN;
	}
	if (ts.isPropertyAccessExpression(e)) {
		if (e.name.text === "length") return syn("other");
		return synOfMember(memberOf(containerOfExpr(e.expression, depth + 1), e.name.text), depth + 1);
	}
	if (ts.isElementAccessExpression(e)) return SYN_UNKNOWN;
	if (ts.isIdentifier(e)) {
		const d = declOf(e);
		if (!d) return SYN_UNKNOWN;
		if ((ts.isVariableDeclaration(d) || ts.isParameter(d) || ts.isPropertyDeclaration(d)) && d.type) return synOfTypeNode(d.type, depth + 1);
		if ((ts.isVariableDeclaration(d) || ts.isParameter(d) || ts.isPropertyDeclaration(d)) && d.initializer) return synOfExpr(d.initializer, depth + 1);
		if (ts.isVariableDeclaration(d) && ts.isVariableDeclarationList(d.parent) && ts.isForOfStatement(d.parent.parent)) {
			const src = synOfExpr(d.parent.parent.expression, depth + 1);
			return src.kind === "string" ? syn("string") : SYN_UNKNOWN;
		}
		if (ts.isPropertySignature(d) && d.type) return synOfTypeNode(d.type, depth + 1);
		if (ts.isClassDeclaration(d) || ts.isFunctionDeclaration(d)) return syn("other");
		if (ts.isEnumDeclaration(d)) return syn("other", false, true);
		return SYN_UNKNOWN;
	}
	return SYN_UNKNOWN;
};
const kindOf = (e: ts.Expression, method: string): Kind => {
	let k: Kind;
	if (TYPES === "oracle") {
		k = synOfExpr(e).kind;
		if (k === "unknown" && METHOD_MATTERS.has(method)) {
			if (oraclePass === 1) need(e);
			else k = fromOracle(e)?.kind ?? k;
		}
	} else k = SYNTACTIC ? synOfExpr(e).kind : kindOfType(checker.getTypeAtLocation(e));
	count(`kind: ${k}`);
	return k;
};
const tupleOf = (e: ts.Expression): boolean => {
	let r: boolean;
	if (TYPES === "oracle") {
		r = synOfExpr(e).tuple;
		if (!r) {
			if (oraclePass === 1) need(e);
			else r = fromOracle(e)?.tuple ?? false;
		}
	} else if (SYNTACTIC) r = synOfExpr(e).tuple;
	else {
		const t = checker.getTypeAtLocation(e);
		r = isTuple(t) || (t.isUnion() && t.types.length > 0 && t.types.every(isTuple));
	}
	if (r) count("types: tuple");
	return r;
};
const closedOf = (e: ts.Expression): boolean => {
	let r: boolean;
	if (TYPES === "oracle") {
		r = synOfExpr(e).closed;
		if (!r) {
			if (oraclePass === 1) need(e);
			else r = fromOracle(e)?.closed ?? false;
		}
	} else r = SYNTACTIC ? synOfExpr(e).closed : closedObject(checker.getTypeAtLocation(e));
	if (r) count("types: closed object");
	return r;
};

const symOf = (node: ts.Node): ts.Symbol | undefined => {
	let sym = checker.getSymbolAtLocation(node);
	if (!sym) return undefined;
	if (sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym);
	return sym;
};
const declOf = (node: ts.Node): ts.Declaration | undefined => symOf(node)?.declarations?.[0];
const fnOfDecl = (d: ts.Declaration | undefined): Fn | undefined => {
	if (!d) return undefined;
	if (isFn(d) && d.body) return d;
	if (ts.isVariableDeclaration(d) && d.initializer && isFn(d.initializer) && d.initializer.body) return d.initializer;
	if ((ts.isPropertyAssignment(d) || ts.isPropertyDeclaration(d)) && d.initializer && isFn(d.initializer) && d.initializer.body) return d.initializer;
	if (ts.isClassDeclaration(d) || ts.isClassExpression(d)) {
		const ctor = d.members.find(ts.isConstructorDeclaration);
		return ctor?.body ? ctor : undefined;
	}
	return undefined;
};
const isRestParam = (n: ts.Node) => {
	const d = declOf(n);
	return !!d && ts.isParameter(d) && !!d.dotDotDotToken;
};
const unwrap = (e: ts.Expression): ts.Expression =>
	ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) || ts.isNonNullExpression(e) || ts.isTypeAssertionExpression(e) ? unwrap(e.expression) : e;

const isNumericConstant = (e: ts.Expression): boolean => {
	e = unwrap(e);
	if (ts.isNumericLiteral(e)) return true;
	if (ts.isPrefixUnaryExpression(e)) return isNumericConstant(e.operand);
	if (ts.isBinaryExpression(e)) return isNumericConstant(e.left) && isNumericConstant(e.right);
	if (ts.isPropertyAccessExpression(e) && e.name.text === "length") return constantSized(e.expression);
	if (ts.isIdentifier(e) || ts.isPropertyAccessExpression(e)) {
		const d = declOf(ts.isPropertyAccessExpression(e) ? e.name : e);
		if (d && ts.isVariableDeclaration(d) && d.initializer && ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const) return isNumericConstant(d.initializer);
		if (d && ts.isPropertyDeclaration(d) && d.initializer && d.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword)) return isNumericConstant(d.initializer);
		if (d && ts.isEnumMember(d)) return true;
	}
	return false;
};
const isEnumObject = (e: ts.Expression): boolean => {
	const s = symOf(e);
	return !!s && !!(s.flags & (ts.SymbolFlags.Enum | ts.SymbolFlags.ConstEnum));
};
const DERIVED_METHODS = new Set(["map", "filter", "slice", "concat", "sort", "toSorted", "reverse", "toReversed", "with", "toSpliced", "flatMap"]);
const returnsConstantSized = (fn: ts.Node): boolean => {
	if (!isFn(fn) || !fn.body) return false;
	if (!ts.isBlock(fn.body)) return constantSized(fn.body as ts.Expression);
	let ok = true;
	let seen = false;
	const visit = (n: ts.Node) => {
		if (isFn(n)) return;
		if (ts.isReturnStatement(n)) {
			seen = true;
			if (!n.expression || !constantSized(n.expression)) ok = false;
		}
		n.forEachChild(visit);
	};
	visit(fn.body);
	return ok && seen;
};
const constantSized = (e: ts.Expression): boolean => {
	e = unwrap(e);
	if (ts.isArrayLiteralExpression(e)) return e.elements.every((el) => !ts.isSpreadElement(el) || constantSized(el.expression));
	if (ts.isConditionalExpression(e)) return constantSized(e.whenTrue) && constantSized(e.whenFalse);
	if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && DERIVED_METHODS.has(e.expression.name.text) && constantSized(e.expression.expression)) {
		const m = e.expression.name.text;
		if (m === "flatMap") return !!e.arguments[0] && returnsConstantSized(e.arguments[0]);
		if (m === "concat") return e.arguments.every(constantSized);
		return true;
	}
	if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return true;
	if (ts.isNewExpression(e) && ts.isIdentifier(e.expression) && (TYPED_ARRAYS.has(e.expression.text) || e.expression.text === "Array") && e.arguments?.length === 1 && isNumericConstant(e.arguments[0])) return true;
	if (ts.isIdentifier(e) || ts.isPropertyAccessExpression(e)) {
		const d = declOf(ts.isPropertyAccessExpression(e) ? e.name : e);
		if (d && ts.isVariableDeclaration(d) && d.initializer && ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const && constantSized(d.initializer)) return true;
		if (d && ts.isPropertyDeclaration(d) && d.initializer && d.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword) && constantSized(d.initializer)) return true;
	}
	if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && ts.isIdentifier(e.expression.expression) && e.expression.expression.text === "Object" && OBJECT_KEYED.has(e.expression.name.text) && e.arguments[0]) {
		const arg = e.arguments[0];
		return isEnumObject(arg) || closedOf(arg) || constantSized(arg);
	}
	return tupleOf(e);
};

type WriteInfo = { kind: "incConst" | "decConst" | "incIdent" | "decIdent" | "other"; ident?: string };
const writesInFn = (body: ts.Node): Map<ts.Symbol, WriteInfo[]> => {
	const out = new Map<ts.Symbol, WriteInfo[]>();
	const add = (target: ts.Expression, info: WriteInfo) => {
		const t = unwrap(target);
		const sym = ts.isIdentifier(t) ? symOf(t) : ts.isPropertyAccessExpression(t) ? symOf(t.name) : ts.isElementAccessExpression(t) ? symOf(unwrap(t.expression)) : undefined;
		if (!sym) return;
		out.set(sym, [...(out.get(sym) ?? []), info]);
	};
	const visit = (n: ts.Node) => {
		if (isFn(n)) return;
		if (ts.isBinaryExpression(n) && ts.isAssignmentOperator(n.operatorToken.kind)) {
			const k = n.operatorToken.kind;
			const r = unwrap(n.right);
			if (k === ts.SyntaxKind.PlusEqualsToken || k === ts.SyntaxKind.MinusEqualsToken) {
				const inc = k === ts.SyntaxKind.PlusEqualsToken;
				if (isNumericConstant(r)) add(n.left, { kind: inc ? "incConst" : "decConst" });
				else if (ts.isIdentifier(r)) add(n.left, { kind: inc ? "incIdent" : "decIdent", ident: r.text });
				else add(n.left, { kind: "other" });
			} else if (k === ts.SyntaxKind.EqualsToken && (ts.isArrayLiteralExpression(n.left) || ts.isObjectLiteralExpression(n.left))) {
				for (const id of readsOf(n.left)) out.set(id, [...(out.get(id) ?? []), { kind: "other" }]);
			} else add(n.left, { kind: "other" });
		}
		if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) add(n.operand, { kind: n.operator === ts.SyntaxKind.PlusPlusToken ? "incConst" : "decConst" });
		if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && MUTATORS.has(n.expression.name.text)) add(n.expression.expression, { kind: "other" });
		if (ts.isDeleteExpression(n)) add(n.expression, { kind: "other" });
		n.forEachChild(visit);
	};
	visit(body);
	return out;
};
const readsOf = (node: ts.Node, out = new Set<ts.Symbol>()): Set<ts.Symbol> => {
	if (ts.isIdentifier(node) && !(ts.isPropertyAccessExpression(node.parent) && node.parent.name === node)) {
		const s = symOf(node);
		if (s) out.add(s);
	}
	node.forEachChild((c) => readsOf(c, out));
	return out;
};
const MUTATORS = new Set(["add", "set", "push", "unshift", "delete", "clear", "pop", "shift", "splice", "sort", "reverse", "fill", "copyWithin"]);
type Budget = { dir: "up" | "down"; text: string; scope?: ts.IterationStatement };
type BudgetContext = { budgets: Map<ts.Symbol, Budget>; writes: Map<ts.Symbol, WriteInfo[]>; fn: Fn };
let budgetContext: BudgetContext | undefined;
const enclosingFn = (n: ts.Node): ts.Node | undefined => {
	for (let p = n.parent; p; p = p.parent) if (isFn(p)) return p;
	return undefined;
};
const budgetScope = (sym: ts.Symbol, fn: Fn): { ok: boolean; scope?: ts.IterationStatement } => {
	const d = sym.declarations?.[0];
	if (!d) return { ok: false };
	if (ts.isParameter(d)) return { ok: d.parent === fn };
	if (!ts.isVariableDeclaration(d) || enclosingFn(d) !== fn) return { ok: false };
	if (!(ts.getCombinedNodeFlags(d) & (ts.NodeFlags.Let | ts.NodeFlags.Const))) return { ok: false };
	if (ts.isVariableDeclarationList(d.parent) && ts.isForStatement(d.parent.parent) && d.parent.parent.initializer === d.parent) return { ok: true, scope: d.parent.parent };
	for (let p: ts.Node | undefined = d.parent; p && p !== fn; p = p.parent) if (ts.isIterationStatement(p, false)) return { ok: true, scope: p };
	return { ok: true };
};
const pendingScoped = new Map<ts.Node, Part>();
const isAncestor = (a: ts.Node, n: ts.Node): boolean => {
	for (let p = n.parent; p; p = p.parent) if (p === a) return true;
	return false;
};
const monotoneDir = (sym: ts.Symbol, writes: Map<ts.Symbol, WriteInfo[]>): "up" | "down" | undefined => {
	const w = writes.get(sym) ?? [];
	if (w.length === 0) return undefined;
	if (w.every((x) => x.kind === "incConst" || x.kind === "incIdent")) return "up";
	if (w.every((x) => x.kind === "decConst" || x.kind === "decIdent")) return "down";
	return undefined;
};
const invariantIn = (e: ts.Expression, writes: Map<ts.Symbol, WriteInfo[]>): boolean => {
	for (const s of readsOf(e)) if ((writes.get(s) ?? []).length > 0) return false;
	return true;
};
const conjuncts = (e: ts.Expression): ts.Expression[] => {
	e = unwrap(e);
	if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) return [...conjuncts(e.left), ...conjuncts(e.right)];
	return [e];
};
const LT = new Set([ts.SyntaxKind.LessThanToken, ts.SyntaxKind.LessThanEqualsToken]);
const GT = new Set([ts.SyntaxKind.GreaterThanToken, ts.SyntaxKind.GreaterThanEqualsToken]);
const collectBudgets = (fn: Fn): BudgetContext => {
	const writes = writesInFn(fn.body!);
	const budgets = new Map<ts.Symbol, Budget>();
	const consider = (cond: ts.Expression | undefined) => {
		if (!cond) return;
		for (const c of conjuncts(cond)) {
			if (!ts.isBinaryExpression(c)) continue;
			const [l, r] = [unwrap(c.left), unwrap(c.right)];
			const k = c.operatorToken.kind;
			const tryPair = (counter: ts.Expression, bound: ts.Expression, dirIfCounterLess: "up" | "down") => {
				if (!ts.isIdentifier(counter)) return;
				const sym = symOf(counter);
				if (!sym || budgets.has(sym)) return;
				const where = budgetScope(sym, fn);
				if (!where.ok) return;
				if (monotoneDir(sym, writes) !== dirIfCounterLess) return;
				if (!invariantIn(bound, writes)) return;
				budgets.set(sym, { dir: dirIfCounterLess, text: c.getText().replace(/\s+/g, " "), scope: where.scope });
			};
			if (LT.has(k)) {
				tryPair(l, r, "up");
				tryPair(r, l, "down");
			} else if (GT.has(k)) {
				tryPair(l, r, "down");
				tryPair(r, l, "up");
			}
		}
	};
	const visit = (n: ts.Node) => {
		if (isFn(n)) return;
		if (ts.isWhileStatement(n) || ts.isDoStatement(n)) consider(n.expression);
		if (ts.isForStatement(n)) consider(n.condition);
		n.forEachChild(visit);
	};
	visit(fn.body!);
	return { budgets, writes, fn };
};
let shareSyms: ts.Symbol[] = [];
const isZero = (e: ts.Expression) => ts.isNumericLiteral(unwrap(e)) && Number((unwrap(e) as ts.NumericLiteral).text) === 0;
const shareSized = (e: ts.Expression): boolean => {
	if (shareSyms.length === 0) return false;
	e = unwrap(e);
	if (ts.isIdentifier(e)) {
		const sym = symOf(e);
		if (sym && shareSyms.includes(sym)) return true;
		const d = declOf(e);
		return !!d && ts.isVariableDeclaration(d) && !!d.initializer && !!(ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const) && shareSized(d.initializer);
	}
	if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.PlusToken) return (shareSized(e.left) && isNumericConstant(e.right)) || (isNumericConstant(e.left) && shareSized(e.right));
	if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && (e.expression.name.text === "subarray" || e.expression.name.text === "slice") && e.arguments.length === 2) {
		const [a, b] = e.arguments.map(unwrap);
		if (isZero(a) && shareSized(b)) return true;
		if (ts.isBinaryExpression(b) && b.operatorToken.kind === ts.SyntaxKind.PlusToken && ((sameText(b.left, a) && shareSized(b.right)) || (sameText(b.right, a) && shareSized(b.left)))) return true;
	}
	return false;
};
const advanceOf = (e: ts.Expression): { sym: ts.Symbol; dir: "up" | "down"; ident?: string; identSym?: ts.Symbol; constant: boolean } | undefined => {
	e = unwrap(e);
	if ((ts.isPrefixUnaryExpression(e) || ts.isPostfixUnaryExpression(e)) && ts.isIdentifier(e.operand) && (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
		const sym = symOf(e.operand);
		return sym ? { sym, dir: e.operator === ts.SyntaxKind.PlusPlusToken ? "up" : "down", constant: true } : undefined;
	}
	if (ts.isBinaryExpression(e) && ts.isIdentifier(e.left) && (e.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken || e.operatorToken.kind === ts.SyntaxKind.MinusEqualsToken)) {
		const sym = symOf(e.left);
		if (!sym) return undefined;
		const dir = e.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken ? "up" : "down";
		const r = unwrap(e.right);
		if (isNumericConstant(r)) return { sym, dir, constant: true };
		if (ts.isIdentifier(r)) return { sym, dir, ident: r.text, identSym: symOf(r), constant: false };
	}
	return undefined;
};
const hasContinueAtLevel = (body: ts.Node): boolean => {
	let found = false;
	const visit = (n: ts.Node) => {
		if (found || isFn(n) || ts.isIterationStatement(n, false)) return;
		if (ts.isContinueStatement(n)) found = true;
		n.forEachChild(visit);
	};
	visit(body);
	return found;
};
type Spend = { text: string; share?: ts.Symbol; scope?: ts.IterationStatement };
const spentBudget = (loop: ts.IterationStatement): Spend | undefined => {
	const ctx = budgetContext;
	if (!ctx || ctx.budgets.size === 0) return undefined;
	const spends = (e: ts.Expression | undefined): Spend | undefined => {
		if (!e) return undefined;
		const a = advanceOf(e);
		if (!a) return undefined;
		const b = ctx.budgets.get(a.sym);
		if (!b || b.dir !== a.dir) return undefined;
		if (a.constant) return { text: b.text, scope: b.scope };
		const g = a.identSym;
		const d = g?.declarations?.[0];
		const stable = !!g && !!d && ((ts.isVariableDeclaration(d) && !!(ts.getCombinedNodeFlags(d) & ts.NodeFlags.Const)) || (ts.isParameter(d) && (ctx.writes.get(g) ?? []).length === 0));
		return stable ? { text: `${b.text}, by ${a.ident}`, share: g, scope: b.scope } : { text: `${b.text}, by ${a.ident}`, scope: b.scope };
	};
	if (ts.isForStatement(loop)) {
		const viaIncrementor = spends(loop.incrementor);
		if (viaIncrementor) return viaIncrementor;
	}
	const body = loop.statement;
	const statements = ts.isBlock(body) ? body.statements : [body];
	if (!hasContinueAtLevel(body)) {
		for (const st of statements) {
			if (ts.isExpressionStatement(st)) {
				const r = spends(st.expression);
				if (r) return r;
			}
		}
	}
	return undefined;
};

type PerfTag = "ignore" | "hot" | "cold" | "bounded" | `O(${string})` | `max O(${string})`;
const NO_TAGS: ReadonlySet<PerfTag> = new Set();
const parseCostTag = (t: string): Cost | undefined => {
	const m = t.replace(/\s+/g, "").match(/^O\((1|logN|N(?:\^(\d+))?(logN)?)\)$/);
	if (!m) return undefined;
	if (m[1] === "1") return ONE;
	if (m[1] === "logN") return LOG;
	return { n: m[2] ? Number(m[2]) : 1, log: m[3] ? 1 : 0 };
};
const maxTagOf = (tags: ReadonlySet<PerfTag>): { text: string; cost: Cost } | undefined => {
	for (const t of tags) {
		if (!t.startsWith("max ")) continue;
		const c = parseCostTag(t.slice(4));
		if (c) return { text: t.slice(4), cost: c };
	}
	return undefined;
};
const costTagOf = (tags: ReadonlySet<PerfTag>): { text: string; cost: Cost } | undefined => {
	for (const t of tags) {
		if (t.startsWith("max ")) continue;
		const c = parseCostTag(t);
		if (c) return { text: t.replace(/\s+/g, " "), cost: c };
	}
	return undefined;
};
const tagCache = new Map<ts.Node, Set<PerfTag>>();
const topAt = (n: ts.Node): ts.Node => {
	let t = n;
	while (t.parent && !ts.isSourceFile(t.parent) && t.parent.getFullStart() === t.getFullStart()) t = t.parent;
	return t;
};
const commentTags = (n: ts.Node): Set<PerfTag> => {
	const out = new Set<PerfTag>();
	const text = n.getSourceFile().text;
	for (const r of ts.getLeadingCommentRanges(text, n.getFullStart()) ?? []) {
		for (const m of text.slice(r.pos, r.end).matchAll(/@perf\s+(ignore\b|hot\b|cold\b|bounded\b|max\s+O\([^)]*\)|O\([^)]*\))/g)) out.add(m[1].replace(/\s+/g, " ") as PerfTag);
	}
	return out;
};
const perfTags = (n: ts.Node): ReadonlySet<PerfTag> => {
	if (topAt(n) !== n) return NO_TAGS;
	const cached = tagCache.get(n);
	if (cached) return cached;
	const tags = commentTags(n);
	tagCache.set(n, tags);
	return tags;
};
const statementsOf = (b: ts.Node): readonly ts.Node[] => (ts.isBlock(b) || ts.isCaseClause(b) || ts.isDefaultClause(b) ? b.statements : ts.isCatchClause(b) ? b.block.statements : [b]);
const isHotPath = (b: ts.Node): boolean => perfTags(b).has("hot") || statementsOf(b).some((st) => perfTags(st).has("hot"));
const hotPaths = <T extends ts.Node>(kids: readonly T[], what: string): readonly T[] => {
	const hot = kids.filter(isHotPath);
	if (hot.length === 0) return kids;
	count(`@perf hot: ${what}`);
	return hot;
};
const fnTags = (fn: Fn): ReadonlySet<PerfTag> => {
	let n: ts.Node = fn;
	if ((ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) && (ts.isVariableDeclaration(fn.parent) || ts.isPropertyDeclaration(fn.parent) || ts.isPropertyAssignment(fn.parent))) n = fn.parent;
	if (ts.isVariableDeclaration(n) && ts.isVariableDeclarationList(n.parent) && ts.isVariableStatement(n.parent.parent) && n.parent.declarations.length === 1) n = n.parent.parent;
	return commentTags(topAt(n));
};
const hotOnly = <T extends ts.Node>(kids: readonly T[], what: string): readonly T[] => {
	const hot = kids.filter((k) => perfTags(k).has("hot"));
	if (hot.length === 0) return kids;
	count(`@perf hot: ${what}`);
	return hot;
};

const summaries = new Map<string, Result>();
const stack: string[] = [];
let minHit = Infinity;
let pendingCycle: string[] = [];
type Subst = Map<ts.Symbol, Part>;
let currentSubst: Subst = new Map();
const keyOf = (fn: Fn, subst: Subst) => `${fn.getSourceFile().fileName}:${fn.pos}|${[...subst].map(([s, p]) => `${s.getName()}=${fmt(p.cost)}`).sort().join(",")}`;
const summarizeWith = (fn: Fn, subst: Subst, raw = false): Result => {
	const key = keyOf(fn, subst);
	const known = raw ? undefined : summaries.get(key);
	if (known) return known;
	if (!raw) {
		const tags = fnTags(fn);
		if (tags.has("ignore") || tags.has("cold")) {
			count(`@perf ${tags.has("ignore") ? "ignore" : "cold"}: function`);
			const r = empty();
			summaries.set(key, r);
			return r;
		}
		const ct = costTagOf(tags);
		if (ct) {
			count("@perf O(...): function");
			const r = ofPart({ cost: ct.cost, chain: isOne(ct.cost) ? [] : [{ label: `@perf ${ct.text}`, ...loc(fn), cost: ct.cost }] });
			summaries.set(key, r);
			return r;
		}
	}
	const idx = stack.indexOf(key);
	if (idx >= 0) {
		minHit = Math.min(minHit, idx);
		return ofPart({ cost: N, chain: [{ label: `recursive call ${nameOf(fn)}()`, ...loc(fn), cost: N }] });
	}
	const depth = stack.length;
	stack.push(key);
	const saved = currentSubst;
	const savedBudget = budgetContext;
	const savedShare = shareSyms;
	const savedMin = minHit;
	const savedPending = pendingCycle;
	currentSubst = subst;
	budgetContext = fn.body ? collectBudgets(fn) : undefined;
	shareSyms = [];
	minHit = Infinity;
	pendingCycle = [];
	const r = fn.body ? costOf(fn.body) : empty();
	currentSubst = saved;
	budgetContext = savedBudget;
	shareSyms = savedShare;
	stack.pop();
	const hit = minHit;
	const members = pendingCycle;
	pendingCycle = savedPending;
	if (hit < depth) {
		pendingCycle.push(key, ...members);
		minHit = Math.min(savedMin, hit);
		return r;
	}
	minHit = savedMin;
	if (raw) return r;
	summaries.set(key, r);
	for (const m of members) {
		count("recursion cycle: member takes root summary");
		summaries.set(m, { main: cycleTag(r.main, fn), fnExit: cycleTag(r.fnExit, fn), loopExit: cycleTag(r.loopExit, fn) });
	}
	return r;
};
const cycleTag = (p: Part, root: Fn): Part => (isOne(p.cost) ? p : { ...p, chain: [{ label: `[recursion cycle with ${nameOf(root)}()]`, ...loc(root), cost: ONE }, ...p.chain] });
const summarize = (fn: Fn): Result => summarizeWith(fn, new Map());
const inheritedSubst = (fn: Fn): Subst => {
	const out: Subst = new Map();
	for (const [s, p] of currentSubst) {
		const d = s.declarations?.[0];
		if (d && ts.isParameter(d) && d.parent !== fn) out.set(s, p);
	}
	return out;
};
const partOfArg = (arg: ts.Expression | undefined): Part | undefined => {
	if (!arg) return undefined;
	arg = unwrap(arg);
	if (isFn(arg)) return total(summarizeWith(arg, inheritedSubst(arg)));
	if (ts.isIdentifier(arg) || ts.isPropertyAccessExpression(arg)) {
		const d = declOf(ts.isPropertyAccessExpression(arg) ? arg.name : arg);
		if (d && ts.isParameter(d) && ts.isIdentifier(arg)) return currentSubst.get(symOf(arg)!);
		const fn = fnOfDecl(d);
		if (fn) return total(summarize(fn));
	}
	return undefined;
};
const callbackPart = (arg: ts.Expression | undefined): Part => partOfArg(arg) ?? none();
const callUser = (fn: Fn, callArgs: readonly ts.Expression[]): Part => {
	const subst: Subst = new Map();
	if (CALLBACKS) {
		fn.parameters.forEach((p, i) => {
			if (p.dotDotDotToken || !ts.isIdentifier(p.name)) return;
			const part = partOfArg(callArgs[i]);
			if (part && !isOne(part.cost)) {
				const s = symOf(p.name);
				if (s) subst.set(s, part);
			}
		});
	}
	return total(subst.size > 0 ? summarizeWith(fn, subst) : summarize(fn));
};

const loopLabel = (n: ts.Node) => (ts.isForOfStatement(n) ? "for-of" : ts.isForInStatement(n) ? "for-in" : ts.isForStatement(n) ? "for" : ts.isWhileStatement(n) ? "while" : "do-while");
const nest = (label: string, node: ts.Node, factor: Cost, inner: Part): Part => ({ cost: mul(factor, inner.cost), chain: [{ label, ...loc(node), cost: factor }, ...inner.chain] });
const short = (n: ts.Node) => {
	const t = n.getText().replace(/\s+/g, " ");
	return t.length > 40 ? t.slice(0, 37) + "..." : t;
};
const endsIn = (n: ts.Node | undefined): "return" | "throw" | "break" | undefined => {
	if (!n) return undefined;
	if (ts.isReturnStatement(n)) return "return";
	if (ts.isThrowStatement(n)) return "throw";
	if (ts.isBreakStatement(n)) return "break";
	if (ts.isBlock(n)) return endsIn(n.statements.at(-1));
	if (ts.isIfStatement(n)) {
		const a = endsIn(n.thenStatement);
		const b = endsIn(n.elseStatement);
		return a && b ? (a === b ? a : "return") : undefined;
	}
	return undefined;
};
const insideLoop = (n: ts.Node): boolean => {
	for (let p = n.parent; p && !isFn(p); p = p.parent) if (ts.isIterationStatement(p, false)) return true;
	return false;
};

const norm = (n: ts.Node | undefined) => n?.getText().replace(/\s+/g, "") ?? "";
const sameText = (a: ts.Node | undefined, b: ts.Node | undefined) => !!a && !!b && norm(a) === norm(b);
const loopVarOf = (loop: ts.ForStatement): { name: ts.Identifier; init: ts.Expression } | undefined => {
	const i = loop.initializer;
	if (!i) return undefined;
	if (ts.isVariableDeclarationList(i) && i.declarations.length === 1) {
		const d = i.declarations[0];
		if (ts.isIdentifier(d.name) && d.initializer) return { name: d.name, init: d.initializer };
	}
	if (ts.isBinaryExpression(i) && i.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(i.left)) return { name: i.left, init: i.right };
	return undefined;
};
const MUL_ASSIGN = new Set([ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.SlashEqualsToken, ts.SyntaxKind.LessThanLessThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken]);
const MUL_OPS = new Set([ts.SyntaxKind.AsteriskToken, ts.SyntaxKind.SlashToken, ts.SyntaxKind.LessThanLessThanToken, ts.SyntaxKind.GreaterThanGreaterThanToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken]);
const isGeometric = (value: ts.Expression, v: string): boolean => {
	value = unwrap(value);
	if (ts.isBinaryExpression(value) && MUL_OPS.has(value.operatorToken.kind)) {
		const l = unwrap(value.left);
		return ts.isIdentifier(l) && l.text === v && isNumericConstant(value.right);
	}
	if (ts.isCallExpression(value) && ["Math.floor", "Math.ceil", "Math.trunc"].includes(norm(value.expression)) && value.arguments[0]) return isGeometric(value.arguments[0], v);
	return false;
};
const isMultiplicativeUpdate = (e: ts.Expression | undefined, v: string): boolean => {
	if (!e) return false;
	e = unwrap(e);
	if (!ts.isBinaryExpression(e) || !ts.isIdentifier(e.left) || e.left.text !== v) return false;
	if (MUL_ASSIGN.has(e.operatorToken.kind)) return isNumericConstant(e.right);
	if (e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return isGeometric(e.right, v);
	return false;
};
const boundOfFor = (loop: ts.ForStatement): { factor: Cost; why: string } => {
	const lv = loopVarOf(loop);
	if (lv && isMultiplicativeUpdate(loop.incrementor, lv.name.text)) return { factor: LOG, why: "geometric step" };
	const cond = loop.condition ? unwrap(loop.condition) : undefined;
	if (lv && cond && ts.isBinaryExpression(cond) && LT.has(cond.operatorToken.kind) && ts.isIdentifier(unwrap(cond.left)) && (unwrap(cond.left) as ts.Identifier).text === lv.name.text) {
		const b = unwrap(cond.right);
		if (shareSized(b)) return { factor: ONE, why: "share of budget" };
		if (ts.isBinaryExpression(b) && b.operatorToken.kind === ts.SyntaxKind.PlusToken && ((sameText(b.left, lv.init) && shareSized(b.right)) || (sameText(b.right, lv.init) && shareSized(b.left)))) return { factor: ONE, why: "share of budget" };
	}
	if (cond && ts.isBinaryExpression(cond)) {
		const sides = [cond.left, cond.right].map(unwrap);
		if (sides.some(isNumericConstant)) return { factor: ONE, why: "constant bound" };
		if (lv) {
			const bound = sides.find((s) => !(ts.isIdentifier(s) && s.text === lv.name.text));
			if (bound && ts.isBinaryExpression(bound) && (bound.operatorToken.kind === ts.SyntaxKind.PlusToken || bound.operatorToken.kind === ts.SyntaxKind.MinusToken)) {
				const [l, r] = [unwrap(bound.left), unwrap(bound.right)];
				if ((sameText(l, lv.init) && isNumericConstant(r)) || (sameText(r, lv.init) && isNumericConstant(l))) return { factor: ONE, why: "constant offset from start" };
			}
		}
	}
	return { factor: N, why: "" };
};
const assignmentsTo = (body: ts.Node, names: Set<string>): Array<{ name: string; kind: "geometric" | "assign" | "other"; value?: ts.Expression }> => {
	const out: Array<{ name: string; kind: "geometric" | "assign" | "other"; value?: ts.Expression }> = [];
	const visit = (n: ts.Node) => {
		if (isFn(n)) return;
		if (ts.isBinaryExpression(n) && ts.isAssignmentOperator(n.operatorToken.kind) && ts.isIdentifier(n.left) && names.has(n.left.text)) {
			if (isMultiplicativeUpdate(n, n.left.text)) out.push({ name: n.left.text, kind: "geometric" });
			else if (n.operatorToken.kind === ts.SyntaxKind.EqualsToken) out.push({ name: n.left.text, kind: "assign", value: n.right });
			else out.push({ name: n.left.text, kind: "other" });
		}
		if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && ts.isIdentifier(n.operand) && names.has(n.operand.text)) out.push({ name: n.operand.text, kind: "other" });
		n.forEachChild(visit);
	};
	visit(body);
	return out;
};
const midpointNames = (body: ts.Node, names: Set<string>): Set<string> => {
	const mids = new Set<string>();
	const visit = (n: ts.Node) => {
		if (isFn(n)) return;
		if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name) && n.initializer) {
			const text = norm(n.initializer);
			const mentions = [...names].filter((x) => new RegExp(`\\b${x}\\b`).test(text));
			if (mentions.length >= 2 && (/>>>?1\b/.test(text) || /\/2\b/.test(text))) mids.add(n.name.text);
		}
		n.forEachChild(visit);
	};
	visit(body);
	return mids;
};
const boundOfWhile = (loop: ts.WhileStatement | ts.DoStatement): { factor: Cost; why: string } => {
	const cond = unwrap(loop.expression);
	const names = new Set<string>();
	const collect = (n: ts.Node) => {
		if (ts.isIdentifier(n) && !(ts.isPropertyAccessExpression(n.parent) && n.parent.name === n)) names.add(n.text);
		n.forEachChild(collect);
	};
	collect(cond);
	if (names.size === 0) return { factor: N, why: "" };
	const writes = assignmentsTo(loop.statement, names);
	if (writes.length === 0) return { factor: N, why: "" };
	const mids = midpointNames(loop.statement, names);
	const halving = writes.every((w) => {
		if (w.kind === "geometric") return true;
		if (w.kind !== "assign" || !w.value) return false;
		const r = unwrap(w.value);
		if (ts.isIdentifier(r) && mids.has(r.text)) return true;
		if (ts.isBinaryExpression(r)) {
			const l = unwrap(r.left);
			return ts.isIdentifier(l) && mids.has(l.text) && isNumericConstant(r.right);
		}
		return false;
	});
	return halving ? { factor: LOG, why: "halving" } : { factor: N, why: "" };
};
const stats = new Map<string, number>();
const count = (k: string) => stats.set(k, (stats.get(k) ?? 0) + 1);
const boundSeen = new Set<ts.Node>();
const boundOf = (loop: ts.IterationStatement): { factor: Cost; why: string } => {
	const r = boundOfInner(loop);
	if (!boundSeen.has(loop)) {
		boundSeen.add(loop);
		count(`loop ${loopLabel(loop)}: ${r.why || (r.factor.log ? "log" : "N")}`);
	}
	return r;
};
const boundOfInner = (loop: ts.IterationStatement): { factor: Cost; why: string } => {
	if (perfTags(loop).has("bounded")) return { factor: ONE, why: "@perf bounded" };
	if (endsIn(loop.statement)) return { factor: ONE, why: "single iteration" };
	if (ts.isForOfStatement(loop)) return constantSized(loop.expression) ? { factor: ONE, why: "constant collection" } : shareSized(loop.expression) ? { factor: ONE, why: "share of budget" } : { factor: N, why: "" };
	if (ts.isForInStatement(loop)) return constantSized(loop.expression) || closedOf(loop.expression) ? { factor: ONE, why: "closed object type" } : { factor: N, why: "" };
	if (ts.isForStatement(loop)) return boundOfFor(loop);
	if (ts.isWhileStatement(loop) || ts.isDoStatement(loop)) return boundOfWhile(loop);
	return { factor: N, why: "" };
};

const costOf = (node: ts.Node): Result => {
	if (isFn(node)) return empty();
	if (ts.isClassDeclaration(node) || ts.isClassExpression(node)) return empty();
	if (ts.isTypeNode(node) || ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) return empty();
	const tags = perfTags(node);
	if (tags.has("ignore") || tags.has("cold")) {
		count(`@perf ${tags.has("ignore") ? "ignore" : "cold"}: statement`);
		return empty();
	}
	if (tags.has("bounded") && !ts.isIterationStatement(node, false)) {
		count("@perf bounded: statement");
		return empty();
	}
	const ct = costTagOf(tags);
	if (ct && !ts.isIterationStatement(node, false)) {
		count("@perf O(...): statement");
		return ofPart({ cost: ct.cost, chain: isOne(ct.cost) ? [] : [{ label: `@perf ${ct.text}`, ...loc(node), cost: ct.cost }] });
	}
	if (ct) {
		count("@perf O(...): loop");
		return ofPart({ cost: ct.cost, chain: isOne(ct.cost) ? [] : [{ label: `@perf ${ct.text}`, ...loc(node), cost: ct.cost }] });
	}

	if (ts.isIfStatement(node)) {
		const branches = hotPaths([node.thenStatement, ...(node.elseStatement ? [node.elseStatement] : [])], "branch");
		let acc = costOf(node.expression);
		for (const b of branches) acc = merge(acc, branchResult(b, node));
		return acc;
	}
	if (ts.isSwitchStatement(node)) {
		let acc = costOf(node.expression);
		for (const c of hotPaths(node.caseBlock.clauses, "case")) acc = merge(acc, branchResult(c, node));
		return acc;
	}
	if (ts.isTryStatement(node)) {
		const parts: ts.Node[] = [node.tryBlock, ...(node.catchClause ? [node.catchClause] : []), ...(node.finallyBlock ? [node.finallyBlock] : [])];
		let acc = empty();
		for (const b of hotPaths(parts, "try")) acc = merge(acc, costOf(b));
		return acc;
	}
	if (ts.isBlock(node) || ts.isModuleBlock(node) || ts.isCaseClause(node) || ts.isDefaultClause(node)) {
		let acc = ts.isCaseClause(node) ? costOf(node.expression) : empty();
		for (const st of hotOnly(node.statements, "block")) acc = merge(acc, costOf(st));
		return acc;
	}

	if (ts.isIterationStatement(node, false)) {
		let sibling = empty();
		node.forEachChild((c) => {
			if (c !== node.statement) sibling = merge(sibling, costOf(c));
		});
		const { factor, why } = boundOf(node);
		const spend = isOne(factor) ? undefined : spentBudget(node);
		const budget = spend?.scope === node ? undefined : spend;
		if (budget?.share) shareSyms.push(budget.share);
		const bodyRaw = costOf(node.statement);
		if (budget?.share) shareSyms.pop();
		const hoisted = pendingScoped.get(node);
		pendingScoped.delete(node);
		const body: Result = hoisted ? { ...bodyRaw, main: maxPart(bodyRaw.main, hoisted) } : bodyRaw;
		if (isOne(factor)) return { main: maxPart(maxPart(sibling.main, body.main), body.loopExit), fnExit: maxPart(sibling.fnExit, body.fnExit), loopExit: sibling.loopExit };
		const scope = budget?.scope && isAncestor(budget.scope, node) ? budget.scope : undefined;
		if (budget) count(`loop ${loopLabel(node)}: budget${budget.share ? " by share" : ""}${scope ? " (scoped)" : ""}`);
		const looped = nest(`${loopLabel(node)}${why ? ` [${why}]` : ""}${budget ? ` [budget: ${budget.text}${scope ? `, per ${loopLabel(scope)} at ${loc(scope).line}` : ""}]` : ""}`, node, factor, body.main);
		if (budget && scope) {
			pendingScoped.set(scope, maxPart(pendingScoped.get(scope) ?? none(), looped));
			return { main: maxPart(sibling.main, body.loopExit), fnExit: maxPart(sibling.fnExit, body.fnExit), loopExit: sibling.loopExit };
		}
		if (budget && insideLoop(node)) return { main: maxPart(sibling.main, body.loopExit), fnExit: maxPart(maxPart(sibling.fnExit, body.fnExit), looped), loopExit: sibling.loopExit };
		return { main: maxPart(maxPart(sibling.main, looped), body.loopExit), fnExit: maxPart(sibling.fnExit, body.fnExit), loopExit: sibling.loopExit };
	}

	if (ts.isReturnStatement(node) || ts.isThrowStatement(node)) {
		const inner = node.expression ? costOf(node.expression) : empty();
		if (insideLoop(node)) return { main: none(), fnExit: total(inner), loopExit: none() };
		return inner;
	}

	if (ts.isSpreadElement(node) || ts.isSpreadAssignment(node)) {
		const inner = costOf(node.expression);
		if (ts.isIdentifier(node.expression) && isRestParam(node.expression)) return inner;
		if (constantSized(node.expression)) return inner;
		return merge(inner, ofPart({ cost: N, chain: [{ label: `spread ...${short(node.expression)}`, ...loc(node), cost: N }] }));
	}

	if (ts.isNewExpression(node)) {
		let acc = empty();
		node.arguments?.forEach((a) => (acc = merge(acc, costOf(a))));
		const fn = fnOfDecl(declOf(node.expression));
		if (fn) {
			const callee = callUser(fn, node.arguments ?? []);
			if (isOne(callee.cost)) return acc;
			return merge(acc, ofPart({ cost: callee.cost, chain: [{ label: `new ${nameOf(fn).replace(/\.constructor$/, "")}()`, ...loc(node), cost: callee.cost, inner: callee.chain }] }));
		}
		const ctor = ts.isIdentifier(node.expression) ? node.expression.text : "";
		if (LINEAR_CONSTRUCTORS.has(ctor) && node.arguments?.length && shareSized(node.arguments[0])) count("share: constructor");
		if (LINEAR_CONSTRUCTORS.has(ctor) && node.arguments?.length && !constantSized(node.arguments[0]) && !isNumericConstant(node.arguments[0]) && !shareSized(node.arguments[0])) {
			return merge(acc, ofPart({ cost: N, chain: [{ label: `new ${ctor}(${short(node.arguments[0])})`, ...loc(node), cost: N }] }));
		}
		return acc;
	}

	if (ts.isCallExpression(node)) {
		let acc = empty();
		node.arguments.forEach((a) => {
			if (!isFn(a)) acc = merge(acc, costOf(a));
		});
		const callee = unwrap(node.expression);
		if (ts.isPropertyAccessExpression(callee)) acc = merge(acc, costOf(callee.expression));

		const calleeName = ts.isPropertyAccessExpression(callee) ? callee.name : callee;
		const decl = declOf(calleeName);
		if (CALLBACKS && decl && ts.isParameter(decl) && ts.isIdentifier(callee)) {
			const p = currentSubst.get(symOf(callee)!);
			if (p && !isOne(p.cost)) return merge(acc, ofPart({ cost: p.cost, chain: [{ label: `call ${callee.text}() [callback parameter]`, ...loc(node), cost: p.cost, inner: p.chain }] }));
			return acc;
		}
		const userFn = fnOfDecl(decl);
		if (userFn) {
			const r = callUser(userFn, node.arguments);
			if (isOne(r.cost)) return acc;
			const recursive = r.chain.length === 1 && r.chain[0].label.startsWith("recursive call");
			return merge(acc, ofPart({ cost: r.cost, chain: recursive ? [{ ...r.chain[0], ...loc(node) }] : [{ label: `call ${nameOf(userFn)}()`, ...loc(node), cost: r.cost, inner: r.chain }] }));
		}

		if (ts.isPropertyAccessExpression(callee)) {
			const method = callee.name.text;
			const recv = callee.expression;
			if (ts.isIdentifier(recv) && GLOBAL_LINEAR[recv.text]?.has(method)) {
				const arg = node.arguments[0];
				const bounded = !!arg && (constantSized(arg) || (recv.text === "Object" && OBJECT_KEYED.has(method) && (isEnumObject(arg) || closedOf(arg))));
				const cb = method === "from" ? callbackPart(node.arguments[1]) : none();
				count(`${recv.text}.${method}: ${bounded ? "bounded" : "N"}`);
				if (bounded) return merge(acc, ofPart(cb));
				return merge(acc, ofPart(nest(`${recv.text}.${method}(${arg ? short(arg) : ""})`, node, N, cb)));
			}
			const kind = kindOf(recv, method);
			const tag = kind === "unknown" ? "?" : "";
			const label = (c: string) => `${short(recv)}.${method}()${tag}${c}`;
			const shared = shareSized(recv) || (method === "set" && !!node.arguments[0] && shareSized(node.arguments[0])) || shareSized(node);
			const bounded = constantSized(recv) || shared;
			if (shared && (kind === "array" || kind === "unknown")) count("share: array method");
			if ((kind === "array" || kind === "unknown") && (ARRAY_NLOGN.has(method) || ARRAY_LINEAR.has(method))) count(`array method: ${bounded ? "bounded" : "N"}`);
			if (kind === "string" && STRING_LINEAR.has(method)) count(`string method: ${bounded ? "bounded" : "N"}`);
			if (kind === "array" || kind === "unknown") {
				if (ARRAY_NLOGN.has(method)) return merge(acc, ofPart(bounded ? callbackPart(node.arguments[0]) : nest(label(" [n log n]"), node, NLOGN, callbackPart(node.arguments[0]))));
				if (ARRAY_LINEAR.has(method)) {
					const cb = CALLBACK_METHODS.has(method) ? callbackPart(node.arguments[0]) : none();
					return merge(acc, ofPart(bounded ? cb : nest(label(""), node, N, cb)));
				}
			}
			if (kind === "set" && SET_LINEAR.has(method)) return merge(acc, ofPart(nest(label(""), node, N, callbackPart(node.arguments[0]))));
			if (kind === "map" && MAP_LINEAR.has(method)) return merge(acc, ofPart(nest(label(""), node, N, callbackPart(node.arguments[0]))));
			if (STRINGS_LINEAR && (kind === "string" || kind === "unknown") && STRING_LINEAR.has(method) && !bounded) return merge(acc, ofPart(nest(label(" [string]"), node, N, none())));
			if (STRINGS_LINEAR && kind === "regexp" && REGEXP_LINEAR.has(method) && node.arguments[0] && !constantSized(node.arguments[0])) return merge(acc, ofPart(nest(label(" [regexp]"), node, N, none())));
			return acc;
		}
		if (ts.isIdentifier(callee) && GLOBAL_FUNCTIONS_LINEAR.has(callee.text)) {
			return merge(acc, ofPart(nest(`${callee.text}()`, node, N, none())));
		}
		return acc;
	}

	let acc = empty();
	node.forEachChild((c) => {
		acc = merge(acc, costOf(c));
	});
	return acc;
};

const branchResult = (body: ts.Node, site: ts.Node): Result => {
	const r = costOf(body);
	const exit = endsIn(body);
	if (exit && insideLoop(site) && !isOne(r.main.cost)) {
		const lifted: Part = { ...r.main, chain: [{ label: `[${exit} branch: runs once per ${exit === "break" ? "loop" : "call"}]`, ...loc(site), cost: ONE }, ...r.main.chain] };
		if (exit === "break") return { main: none(), fnExit: r.fnExit, loopExit: maxPart(r.loopExit, lifted) };
		return { main: none(), fnExit: maxPart(r.fnExit, lifted), loopExit: r.loopExit };
	}
	return r;
};

const reportable: Fn[] = [];
const collect = (node: ts.Node) => {
	if (isFn(node) && node.body) {
		const p = node.parent;
		const inlineCallback = (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) && (ts.isCallExpression(p) || ts.isNewExpression(p));
		if (!inlineCallback && !fnTags(node).has("ignore")) reportable.push(node);
	}
	node.forEachChild(collect);
};
for (const sf of program.getSourceFiles()) {
	if (isProjectFile(sf) && !isTestPath(sf.fileName) && !path.relative(root, sf.fileName).startsWith("..")) collect(sf);
}

if (TYPES === "oracle") {
	oraclePass = 1;
	for (const fn of reportable) {
		summarize(fn);
		const t = fnTags(fn);
		if (t.has("cold") || costTagOf(t)) summarizeWith(fn, new Map(), true);
	}
	const sites = [...needed.values()];
	askOracle(sites);
	console.error(`oracle: ${sites.length} sites asked, ${oracleInfo}`);
	oraclePass = 2;
	summaries.clear();
	stats.clear();
	boundSeen.clear();
	pendingScoped.clear();
}

const printChain = (chain: Factor[], depth: number, out: string[]) => {
	let d = depth;
	for (const f of chain) {
		const isLoop = ["for", "for-of", "for-in", "while", "do-while"].some((k) => f.label === k || f.label.startsWith(k + " "));
		const isCall = f.label.startsWith("call ") || f.label.startsWith("new ") || f.label.startsWith("recursive call ") || f.label.startsWith("@perf ");
		const rel = isLoop ? "in loop" : f.label.startsWith("@perf ") ? "reads as" : isCall ? "calls" : "does";
		const cost = isOne(f.cost) ? "" : isCall ? `  = ${fmt(f.cost)}` : `  x ${fmt(f.cost).slice(2, -1)}`;
		out.push(`${"    ".repeat(d)}${rel} ${f.label.replace(/^(call|new|recursive call) /, "").padEnd(52 - Math.min(d * 4, 32))} ${f.file}:${f.line}${cost}`);
		const multiplies = !isCall && !isOne(f.cost);
		if (f.inner) printChain(f.inner, d, out);
		if (multiplies) d += 1;
	}
};

type Limit = { cost: Cost; text: string };
type Config = { max: Limit; entrypoints: Map<string, Limit>; ignore: RegExp[]; source: string };
const globToRe = (g: string) => new RegExp("^" + g.replace(/[.+^${}()|[\]\\]/g, "\\$&").replace(/\*\*\//g, "(?:.*/)?").replace(/\*\*/g, ".*").replace(/\*/g, "[^/]*") + "$");
const limitOf = (text: unknown, where: string): Limit => {
	const cost = typeof text === "string" ? parseCostTag(text) : undefined;
	if (!cost) throw new Error(`perf-lint: ${where} must be O(1), O(log N), O(N), O(N log N) or O(N^k), got ${JSON.stringify(text)}`);
	return { cost, text: (text as string).replace(/\s+/g, " ") };
};
const packageEntries = (): string[] => {
	const pj = path.join(root, "package.json");
	if (!fs.existsSync(pj)) return [];
	const pkg = JSON.parse(fs.readFileSync(pj, "utf8")) as Record<string, unknown>;
	const targets: string[] = [];
	const add = (v: unknown) => {
		if (typeof v === "string") targets.push(v);
		else if (v && typeof v === "object") for (const x of Object.values(v as Record<string, unknown>)) add(x);
	};
	if (pkg.exports) add(pkg.exports);
	else for (const k of ["source", "types", "module", "main"]) if (typeof pkg[k] === "string") targets.push(pkg[k] as string);
	const found = new Set<string>();
	for (const t of targets) {
		const base = t.replace(/^\.\//, "");
		const candidates = [base, base.replace(/\.d\.ts$/, ".ts").replace(/\.[cm]?js$/, ".ts")];
		for (const c of [...candidates]) if (/^dist\//.test(c)) candidates.push(c.replace(/^dist\//, "src/"));
		for (const c of [...candidates]) if (/\.ts$/.test(c)) candidates.push(c.replace(/\.ts$/, "/index.ts"));
		for (const c of candidates) {
			const abs = path.resolve(root, c);
			if (program.getSourceFile(abs)) {
				found.add(abs);
				break;
			}
		}
	}
	return [...found];
};
const readConfig = (): Config => {
	const explicit = args.find((a) => a.startsWith("--config="))?.slice(9);
	const cfgPath = explicit ? path.resolve(explicit) : path.join(root, "olint.config.json");
	const raw = (fs.existsSync(cfgPath) ? JSON.parse(fs.readFileSync(cfgPath, "utf8")) : {}) as Record<string, unknown>;
	const max = limitOf(raw.max ?? "O(N^2)", "max");
	const entrypoints = new Map<string, Limit>();
	if (raw.entrypoints && typeof raw.entrypoints === "object") {
		for (const [p, m] of Object.entries(raw.entrypoints as Record<string, unknown>)) entrypoints.set(path.resolve(root, p), limitOf(m, `entrypoints["${p}"]`));
	} else for (const p of packageEntries()) entrypoints.set(p, max);
	const ignore = Array.isArray(raw.ignore) ? (raw.ignore as string[]).map(globToRe) : [];
	return { max, entrypoints, ignore, source: fs.existsSync(cfgPath) ? rel(cfgPath) : "defaults" };
};
const config = readConfig();
const ignoredFile = (f: string) => config.ignore.some((re) => re.test(rel(f)));
const fnsOfDecl = (d: ts.Declaration): Fn[] => {
	if (isFn(d) && d.body) return [d];
	if (ts.isVariableDeclaration(d) && d.initializer && isFn(d.initializer) && d.initializer.body) return [d.initializer];
	if (ts.isClassDeclaration(d)) {
		const out: Fn[] = [];
		for (const m of d.members) {
			const hidden = m.modifiers?.some((x) => x.kind === ts.SyntaxKind.PrivateKeyword || x.kind === ts.SyntaxKind.ProtectedKeyword) || (m.name !== undefined && ts.isPrivateIdentifier(m.name));
			if (hidden) continue;
			if (isFn(m) && m.body) out.push(m);
			else if (ts.isPropertyDeclaration(m) && m.initializer && isFn(m.initializer) && m.initializer.body) out.push(m.initializer);
		}
		return out;
	}
	return [];
};
const publicFns = new Map<Fn, { limit: Limit; entry: string }>();
for (const [entryPath, limit] of config.entrypoints) {
	const sf = program.getSourceFile(entryPath);
	if (!sf) {
		console.error(`perf-lint: entrypoint ${rel(entryPath)} is not in the program`);
		continue;
	}
	const mod = checker.getSymbolAtLocation(sf);
	if (!mod) continue;
	for (let sym of checker.getExportsOfModule(mod)) {
		if (sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym);
		for (const d of sym.declarations ?? []) {
			for (const fn of fnsOfDecl(d)) {
				const f = fn.getSourceFile();
				if (!isProjectFile(f) || isTestPath(f.fileName) || ignoredFile(f.fileName) || fnTags(fn).has("ignore")) continue;
				const prev = publicFns.get(fn);
				if (!prev || gt(prev.limit.cost, limit.cost)) publicFns.set(fn, { limit, entry: rel(entryPath) });
			}
		}
	}
}

if (!args.includes("--report")) {
	const checked = [...publicFns].map(([fn, { limit, entry }]) => {
		const own = maxTagOf(fnTags(fn));
		return { fn, entry, limit: own ?? limit, ownLimit: !!own, p: total(summarize(fn)) };
	});
	const over = checked.filter((c) => gt(c.p.cost, c.limit.cost)).sort((a, b) => (gt(a.p.cost, b.p.cost) ? -1 : gt(b.p.cost, a.p.cost) ? 1 : 0));
	const lines: string[] = [];
	lines.push(`# ${rel(configPath)}  ${config.source}: max ${config.max.text}, ${config.entrypoints.size} entrypoint${config.entrypoints.size === 1 ? "" : "s"} (${[...config.entrypoints.keys()].map(rel).join(", ")}), ${checked.length} public functions`);
	lines.push("");
	for (const { fn, p, limit, ownLimit, entry } of over) {
		const l = loc(fn);
		lines.push(`${fmt(p.cost)} > ${limit.text}${ownLimit ? " [@perf max]" : ""}  ${nameOf(fn)}  ${l.file}:${l.line}  via ${entry}`);
		printChain(p.chain, 1, lines);
		lines.push("");
	}
	lines.push(`${over.length} over limit`);
	console.log(lines.join("\n"));
	console.error([...stats].sort((a, b) => b[1] - a[1]).map(([k, v]) => `${String(v).padStart(5)}  ${k}`).join("\n"));
	process.exitCode = over.length > 0 ? 1 : 0;
} else {
const rows = reportable.map((fn) => {
	const tags = fnTags(fn);
	const mark = tags.has("cold") ? "cold" : costTagOf(tags)?.text;
	return { fn, mark, p: total(mark ? summarizeWith(fn, new Map(), true) : summarize(fn)) };
});
const buckets = new Map<string, number>();
for (const { p } of rows) buckets.set(fmt(p.cost), (buckets.get(fmt(p.cost)) ?? 0) + 1);
const out: string[] = [];
out.push(`# ${rel(configPath)}  (${rows.length} functions in ${new Set(rows.map(({ fn }) => fn.getSourceFile().fileName)).size} files)`);
out.push("");
for (const [k, v] of [...buckets].sort((a, b) => b[1] - a[1])) out.push(`${k.padEnd(16)} ${String(v).padStart(4)}`);
out.push("");
const flagged = rows.filter(({ p }) => p.cost.n >= minN || (p.cost.n >= 1 && p.cost.log >= 1)).sort((a, b) => (gt(a.p.cost, b.p.cost) ? -1 : gt(b.p.cost, a.p.cost) ? 1 : 0));
for (const { fn, p, mark } of flagged) {
	const l = loc(fn);
	out.push(`${fmt(p.cost).padEnd(14)} ${nameOf(fn)}${mark ? ` [@perf ${mark}]` : ""}  ${l.file}:${l.line}`);
	printChain(p.chain, 1, out);
	out.push("");
}
console.log(out.join("\n"));
console.error([...stats].sort((a, b) => b[1] - a[1]).map(([k, v]) => `${String(v).padStart(5)}  ${k}`).join("\n"));
}
