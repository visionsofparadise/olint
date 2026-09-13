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

export function ordinaryForLoopCounterExcluded(n: number, xs: number[]): number {
	let sum = 0;
	for (let i = 0; i < n; i++) sum += xs[i];
	return sum;
}

export function shorthandDestructure(xs: number[], n: number, next: () => { i: number }): number {
	let i = 0;
	let total = 0;
	for (const x of xs) {
		while (i < n) {
			total += x;
			i++;
		}
	}
	({ i } = next());
	return total;
}

export namespace BudgetSpace {
	export let limit = 10;
	export function namespaceWrite(xs: number[]): number {
		let i = 0;
		for (const x of xs) {
			while (i < limit) {
				i++;
			}
			BudgetSpace.limit += x;
		}
		return i;
	}
}

export function compoundBound(xs: number[], n: number): number {
	let i = 0;
	let k = 0;
	for (const x of xs) {
		while (i < n - k) {
			i++;
		}
		k += x;
	}
	return i;
}

export function callBound(xs: number[], n: number, size: (a: number) => number): number {
	let i = 0;
	for (const x of xs) {
		while (i < size(n)) {
			i++;
		}
		n += x;
	}
	return i;
}

export function swapPattern(xs: number[], n: number): number {
	let i = 0;
	let j = 0;
	for (const x of xs) {
		while (j < n) {
			j++;
		}
		[i, j] = [x, i];
	}
	return i + j;
}

export function shorthandDefault(xs: number[], next: () => { i?: number }, d: number): number {
	let i = 0;
	for (const x of xs) {
		while (i < d) {
			i++;
		}
		({ i = d } = next());
	}
	return i + xs.length;
}

export namespace BudgetOuter {
	export namespace Inner {
		export let size = 10;
		export function nestedNamespaceWrite(xs: number[]): number {
			let i = 0;
			for (const x of xs) {
				while (i < size) {
					i++;
				}
				BudgetOuter.Inner.size += x;
			}
			return i;
		}
	}
}

export namespace BudgetMerged {
	export let cap = 3;
}
export namespace BudgetMerged {
	export function mergedBlockWrite(xs: number[]): number {
		let i = 0;
		for (const x of xs) {
			while (i < cap) {
				i++;
			}
			BudgetMerged.cap += x;
		}
		return i;
	}
}
