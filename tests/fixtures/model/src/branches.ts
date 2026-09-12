// hot tag on a branch of an if.
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

// hot tag on a case.
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

// hot tag on a try block/catch part.
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

// hot tag on a plain block statement.
export function hotBlockStatement(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	// @perf hot
	for (const row of xs) sum += row.length;
	return sum;
}

// cold tag on a statement.
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

// ignore tag on a statement.
export function ignoredStatementFn(xs: number[][]): number {
	let sum = 0;
	// @perf ignore
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	for (const row of xs) sum += row.length;
	return sum;
}

// ignore tag on a whole function.
// @perf ignore
export function ignoredFunctionTagged(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

// bounded tag on a loop.
export function boundedLoopStatement(xs: number[][], channels: number): number {
	let sum = 0;
	// @perf bounded
	for (let c = 0; c < channels; c++) for (const row of xs) sum += row.length + c;
	return sum;
}

// bounded tag on a non-loop statement.
export function boundedNonLoopStatement(xs: number[][]): number {
	let sum = 0;
	// @perf bounded
	sum += xs.reduce((a, row) => a + row.length, 0);
	for (const row of xs) for (const v of row) sum += v;
	return sum;
}

// O(N log N) tag on a statement.
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

/** @perf max O(N^3) */
export function maxTaggedPublicFn(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

// return inside a loop. The costly operation must happen in a statement
// *before* the return (not inside the returned expression itself), because a
// `return <costed expr>` redirects its own cost straight to the function's
// exit part before the branch-lifting logic ever inspects it.
export function returnInsideLoop(xs: number[][]): number {
	for (const row of xs) {
		if (row.length > 0) {
			const sorted = row.sort((a, b) => a - b);
			return sorted.length;
		}
	}
	return -1;
}

// break inside a loop, likewise needing a nonzero branch cost.
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

// switch whose discriminant expression itself has a nonzero cost.
export function switchDiscriminantCost(xs: number[], target: number): string {
	switch (xs.indexOf(target)) {
		case -1:
			return "missing";
		default:
			return "found";
	}
}
