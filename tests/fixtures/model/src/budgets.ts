// A budget (`i < n`) declared outside any loop, drained one unit at a time by
// an inner while loop nested inside an outer, constant-bounded for loop. The
// outer loop's own counter is a constant-bound loop (excluded from being a
// budget consumer itself, see ordinaryForLoopCounterExcluded below), so the
// drained while loop's cost is what dominates the function's total cost.
export function drainedBudget(n: number, xs: number[]): number {
	let sum = 0;
	let i = 0;
	for (let j = 0; j < 3; j++) {
		while (i < n) {
			sum += xs[i];
			i++;
		}
	}
	return sum;
}

// A budget counter (`i < width`) declared *inside* an enclosing for loop, so
// it resets every outer iteration: a scoped budget attributed back to the
// enclosing "for" loop.
export function scopedBudget(rows: number[][], width: number): number {
	let total = 0;
	for (let r = 0; r < rows.length; r++) {
		const row = rows[r];
		let i = 0;
		while (i < width) {
			total += row[i] ?? 0;
			i++;
		}
	}
	return total;
}

// A budget (`i < n`) drained by a stable identifier `g` (a never-reassigned
// parameter), which makes `g` itself "share-sized" for the remainder of the
// loop body: subarray(0, g), slice(0, g), new Uint8Array(g) and the
// `for (j < g)` loop are all keyed off the same share-sized identifier.
export function shareOfBudget(n: number, g: number, xs: Uint8Array): number {
	let sum = 0;
	let i = 0;
	while (i < n) {
		const chunk = xs.subarray(0, g);
		const chunk2 = xs.slice(0, g);
		const buf = new Uint8Array(g);
		for (let j = 0; j < g; j++) {
			sum += chunk[j] + chunk2[j] + buf[j];
		}
		i += g;
	}
	return sum;
}

// An ordinary for loop: its own counter must not be mistaken for consuming
// some other loop's budget.
export function ordinaryForLoopCounterExcluded(n: number, xs: number[]): number {
	let sum = 0;
	for (let i = 0; i < n; i++) sum += xs[i];
	return sum;
}
