import type { NamedThing } from "./modules/named";

export interface IndexSigThing {
	[key: string]: number;
}
export function forInIndexSig(o: IndexSigThing): number {
	let count = 0;
	for (const k in o) count++;
	return count;
}

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

export function keyofType(k: keyof FullRecord): string {
	return String(k);
}

type AliasBase = { a: number; b: number };
type AliasChain = AliasBase;
export function typeAliasChain(o: AliasChain, matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) for (const v of row) sum += o.a + o.b + v;
	return sum;
}

export function genericWithConstraint<T extends { length: number }>(o: T): number {
	return o.length;
}

export function destructuredParam({ a, b }: { a: number; b: number }): number {
	return a + b;
}

interface HasMethod {
	run: (xs: number[]) => number[];
}
export function callsMethodShapedProperty(o: HasMethod, xs: number[]): number[] {
	return o.run(xs);
}

export function usesNamedThing(o: NamedThing): number {
	return o.value;
}

export function tripleNestedOverLimit(matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}
