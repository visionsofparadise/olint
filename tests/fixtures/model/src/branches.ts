export function hotIfBranch(xs: number[][], fast: boolean): number {
	let sum = 0;
	if (fast) {
		// @perf hot
		for (const row of xs) sum += row.length;
	} else {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function hotCaseBranch(xs: number[][], mode: number): number {
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

export function hotTryBranch(xs: number[][]): number {
	let sum = 0;
	try {
		// @perf hot
		for (const row of xs) sum += row.length;
	} catch {
		for (const row of xs) for (const v of row) sum += v;
	}
	return sum;
}

export function hotBlockStatement(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	// @perf hot
	for (const row of xs) sum += row.length;
	return sum;
}

export function coldStatementFn(xs: number[][]): number {
	let sum = 0;
	// @perf cold
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	for (const row of xs) sum += row.length;
	return sum;
}

/** @perf cold */
export function coldFunctionTagged(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export function ignoredStatementFn(xs: number[][]): number {
	let sum = 0;
	// @perf ignore
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	for (const row of xs) sum += row.length;
	return sum;
}

// @perf ignore
export function ignoredFunctionTagged(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export function boundedLoopStatement(xs: number[][], channels: number): number {
	let sum = 0;
	// @perf bounded
	for (let c = 0; c < channels; c++) for (const row of xs) sum += row.length + c;
	return sum;
}

export function boundedNonLoopStatement(xs: number[][]): number {
	let sum = 0;
	// @perf bounded
	sum += xs.reduce((a, row) => a + row.length, 0);
	for (const row of xs) for (const v of row) sum += v;
	return sum;
}

export function nlognStatementTagged(xs: number[][]): number {
	let sum = 0;
	// @perf O(N log N)
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

/** @perf O(N log N) */
export function nlognFunctionTagged(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export function nlognExpressionStatementTagged(xs: number[][]): number {
	// @perf O(N log N)
	xs.sort((a, b) => a.length - b.length);
	return xs.length;
}

/** @perf max O(N^3) */
export function maxTaggedPublicFn(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export function returnInsideLoop(xs: number[][]): number {
	for (const row of xs) {
		if (row.length > 0) {
			const sorted = row.sort((a, b) => a - b);
			return sorted.length;
		}
	}
	return -1;
}

export function breakInsideLoop(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) {
		if (row.length > 0) {
			sum += row.sort((a, b) => a - b).length;
			break;
		}
	}
	return sum;
}

export function switchDiscriminantCost(xs: number[], target: number): string {
	switch (xs.indexOf(target)) {
		case -1:
			return "missing";
		default:
			return "found";
	}
}
