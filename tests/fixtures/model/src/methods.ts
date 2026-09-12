// One call from each of the six method tables.
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

// regexp method call with a constant argument: should not cost N.
export function regexpConstCall(re: RegExp): boolean {
	return re.test("a-fixed-literal-needle");
}

// regexp method call with a non-constant argument: should cost N.
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

// Method call on a receiver of unknown kind (an untyped/any-ish parameter).
export function unknownReceiverCall(recv: any, needle: number): boolean {
	return recv.includes(needle);
}

// new Set(x) with a non-constant x, wrapped in a real loop so the
// non-constant `new` call-cost shows up in the printed chain.
export function newSetNonConst(rows: number[][]): number {
	let total = 0;
	for (const xs of rows) total += new Set(xs).size;
	return total;
}

// new Map(<constant-sized argument>).
export function newMapConstant(): Map<string, number> {
	return new Map([
		["a", 1],
		["b", 2],
	]);
}
