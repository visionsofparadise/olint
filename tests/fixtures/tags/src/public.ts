export function cubic(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

/** @perf max O(N^3) */
export function acceptedCubic(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) sum += v * w;
	return sum;
}

export const quadratic = (xs: number[][]): number => {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	return sum;
};

export class Engine {
	run(xs: number[][]): number {
		return cubic(xs);
	}

	private helper(xs: number[][]): number {
		return cubic(xs);
	}
}

function notExported(xs: number[][]): number {
	return cubic(xs) + cubic(xs);
}

export const uses = (xs: number[][]) => notExported(xs);
