export interface ClosedThing {
	a: number;
	b: number;
}

export function constantBoundLoop(xs: number[]): number {
	let sum = 0;
	for (let i = 0; i < 10; i++) sum += xs[i] ?? 0;
	return sum;
}

export function constantOffsetFromStart(xs: number[], start: number): number {
	let sum = 0;
	for (let i = start; i < start + 5; i++) sum += xs[i] ?? 0;
	return sum;
}

export function geometricStepLoop(matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) {
		for (let i = 1; i < row.length; i *= 2) sum += row[i];
	}
	return sum;
}

export function whileHalvingShift(matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) {
		let n = row.length;
		while (n > 1) {
			n = n >> 1;
			sum += 1;
		}
	}
	return sum;
}

export function whileHalvingMidpoint(matrix: number[][], target: number): number {
	let found = 0;
	for (const row of matrix) {
		let lo = 0;
		let hi = row.length;
		while (lo < hi) {
			const mid = (lo + hi) >> 1;
			if (row[mid] < target) lo = mid + 1;
			else hi = mid;
		}
		found += lo;
	}
	return found;
}

export function forOfTuple(t: [number, string, boolean]): number {
	let count = 0;
	for (const x of t) count++;
	return count;
}

export function forInClosed(o: ClosedThing): number {
	let count = 0;
	for (const k in o) count++;
	return count;
}

export function forInRecord(o: Record<string, number>): number {
	let count = 0;
	for (const k in o) count++;
	return count;
}

export function singleIterationLoop(xs: number[]): number {
	for (const x of xs) {
		return x;
	}
	return -1;
}

export function labeledLoop(matrix: number[][]): number {
	let count = 0;
	outer: for (const row of matrix) {
		for (const v of row) {
			if (v < 0) continue outer;
			count++;
		}
	}
	return count;
}

export async function forAwaitLoop(xs: AsyncIterable<number>): Promise<number> {
	let sum = 0;
	for await (const x of xs) sum += x;
	return sum;
}

export function unaryHalving(xs: number[], target: number): number {
	let lo = 0;
	let hi = xs.length;
	while (lo < hi) {
		const mid = (lo + hi) >> 1;
		if (~lo) {
			lo = mid + 1;
		} else {
			hi = mid;
		}
	}
	return lo + target;
}
