import type { NamedThing } from "./modules/named";

// Interface with an index signature.
export interface IndexSigThing {
	[key: string]: number;
}
export function forInIndexSig(o: IndexSigThing): number {
	let count = 0;
	for (const k in o) count++;
	return count;
}

// A union of two closed types.
export interface ClosedA {
	a: number;
}
export interface ClosedB {
	b: number;
}
export function unionOfClosed(o: ClosedA | ClosedB, matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) for (const v of row) sum += "a" in o ? o.a : o.b;
	return sum;
}

// Pick, Omit, Readonly.
export interface FullRecord {
	a: number;
	b: string;
	c: boolean;
}
export function pickType(o: Pick<FullRecord, "a" | "b">): string {
	return `${o.a}-${o.b}`;
}
export function omitType(o: Omit<FullRecord, "c">): string {
	return `${o.a}-${o.b}`;
}
export function readonlyType(o: Readonly<FullRecord>): string {
	return `${o.a}`;
}

// keyof.
export function keyofType(k: keyof FullRecord): string {
	return String(k);
}

// A type-alias chain: alias of an alias.
type AliasBase = { a: number; b: number };
type AliasChain = AliasBase;
export function typeAliasChain(o: AliasChain, matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) for (const v of row) sum += o.a + o.b + v;
	return sum;
}

// A generic function with an extends constraint.
export function genericWithConstraint<T extends { length: number }>(o: T): number {
	return o.length;
}

// A destructured parameter.
export function destructuredParam({ a, b }: { a: number; b: number }): number {
	return a + b;
}

// A method-shaped property (a property whose type is a function signature)
// used as a receiver for a costed call.
interface HasMethod {
	run: (xs: number[]) => number[];
}
export function callsMethodShapedProperty(o: HasMethod, xs: number[]): number[] {
	return o.run(xs);
}

// An interface imported from another file in this fixture, used as a
// parameter's type.
export function usesNamedThing(o: NamedThing): number {
	return o.value;
}

// A plain, untagged cubic function: genuinely over the default O(N^2) max,
// so lint mode has at least one real finding.
export function tripleNestedOverLimit(matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}
