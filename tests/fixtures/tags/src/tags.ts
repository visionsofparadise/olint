export function plainNested(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	return sum;
}

export function coldStatement(xs: number[][]): number {
	let sum = 0;
	// @perf cold
	for (const row of xs) for (const v of row) sum += v;
	for (const row of xs) sum += row.length;
	return sum;
}

export function coldBranch(xs: number[][], rebuild: boolean): number {
	let sum = 0;
	if (rebuild) {
		// @perf cold
		for (const row of xs) for (const v of row) sum += v;
	} else {
		for (const row of xs) sum += row.length;
	}
	return sum;
}

export function hotBranch(xs: number[][], fast: boolean): number {
	let sum = 0;
	if (fast) {
		// @perf hot
		for (const row of xs) sum += row.length;
	} else {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function hotStatement(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	// @perf hot
	for (const row of xs) sum += row.length;
	return sum;
}

export function hotCase(xs: number[][], mode: number): number {
	let sum = 0;
	switch (mode) {
		case 0:
			// @perf hot
			for (const row of xs) sum += row.length;
			break;
		default:
			for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function hotTry(xs: number[][]): number {
	let sum = 0;
	try {
		// @perf hot
		for (const row of xs) sum += row.length;
	} catch {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

// @perf ignore
export function ignoredFn(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

/** @perf cold */
export const coldFn = (xs: number[][]): number => {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
};

export function callsIgnoredAndCold(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) sum += ignoredFn([row]) + coldFn([row]);
	return sum;
}

export class Svc {
	// @perf cold
	private rebuild(xs: number[][]): number {
		let sum = 0;
		for (const row of xs) for (const v of row) sum += v;
		return sum;
	}

	run(xs: number[][]): number {
		let sum = 0;
		for (const row of xs) sum += this.rebuild([row]);
		return sum;
	}
}

export function untagged(xs: number[][], fast: boolean): number {
	let sum = 0;
	if (fast) {
		for (const row of xs) sum += row.length;
	} else {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function boundedLoop(xs: number[][], channels: number): number {
	let sum = 0;
	// @perf bounded
	for (let c = 0; c < channels; c++) for (const row of xs) sum += row.length + c;
	return sum;
}

export function costStatement(xs: number[][]): number {
	let sum = 0;
	// @perf O(N)
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

/** @perf O(N) */
export function costFn(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export function callsCostFn(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) sum += costFn([row]);
	return sum;
}

export function hotSecondStatement(xs: number[][], fast: boolean): number {
	let sum = 0;
	if (fast) {
		sum += 1;
		// @perf hot
		for (const row of xs) sum += row.length;
	} else {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function hotSingleStatementBranch(xs: number[][], fast: boolean): number {
	let sum = 0;
	if (fast)
		// @perf hot
		sum += xs.length;
	else for (const row of xs) for (const v of row) sum += v;
	return sum;
}

export function coldFirstOfTwo(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) {
		// @perf cold
		for (const v of row) sum += v;
		for (const v of row) sum -= v;
	}
	return sum;
}
