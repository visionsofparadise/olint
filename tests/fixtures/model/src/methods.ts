export function arrayLinearCall(xs: number[], needle: number): boolean {
	return xs.includes(needle);
}

export function sortMethodCall(xs: number[]): number[] {
	return xs.sort((a, b) => a - b);
}

export function setLinearCall(s: Set<number>, cb: (v: number) => void): void {
	s.forEach(cb);
}

export function mapLinearCall(m: Map<string, number>, cb: (v: number, k: string) => void): void {
	m.forEach(cb);
}

export function stringLinearCall(strings: string[], needle: string): number {
	let total = 0;
	for (const s of strings) total += s.indexOf(needle);
	return total;
}

export function regexpConstCall(re: RegExp): boolean {
	return re.test("a-fixed-literal-needle");
}

export function regexpVarCall(re: RegExp, needles: string[]): number {
	let count = 0;
	for (const needle of needles) if (re.test(needle)) count++;
	return count;
}

export function objectKeysCall(o: Record<string, number>): string[] {
	return Object.keys(o);
}

export function arrayFromCallback(n: number): number[] {
	return Array.from({ length: n }, (_, i) => i * 2);
}

export function jsonParseCall(text: string): unknown {
	return JSON.parse(text);
}

declare const Buffer: { concat(list: unknown[]): unknown };

export function bufferConcatCall(parts: unknown[]): unknown {
	return Buffer.concat(parts);
}

export function structuredCloneCall(items: object[]): unknown[] {
	return items.map((o) => structuredClone(o));
}

export function unknownReceiverCall(recv: any, needle: number): boolean {
	return recv.includes(needle);
}

export function newSetNonConst(rows: number[][]): number {
	let total = 0;
	for (const xs of rows) total += new Set(xs).size;
	return total;
}

export function newMapConstant(): Map<string, number> {
	return new Map([
		["a", 1],
		["b", 2],
	]);
}

function makeUnionSet() {
	return new Set<number>();
}

function makeDoubled() {
	return [1, 2, 3].map((x) => x * 2);
}

export function unionCallback(n: number) {
	const s = makeUnionSet();
	const list = makeDoubled();
	return s.union(() => list.map((x) => x + n));
}

export function spreadRestTupleSet(...rows: [number, number][]) {
	return new Set(...rows);
}

export function spreadRestKeys(...rows: { a: number; b: number }[]) {
	return Object.keys(...rows);
}

export function surrogateCutLabel(prefix: string) {
	return (prefix + "aaaaaaaaaaaaaaaaaaaaaaaaa😀bbbbbbbbb").split(",");
}

export function nextLineLabel(prefix: string) {
	return (prefix + "ab").split(",");
}

class RoundEngine {
	run(xs: number[]): number {
		return xs.indexOf(1);
	}
}

function makeRoundEngine() {
	return new RoundEngine();
}

export function unionHidesCallee(xs: number[]) {
	const s = makeUnionSet();
	return s.union(() => makeRoundEngine().run(xs));
}
