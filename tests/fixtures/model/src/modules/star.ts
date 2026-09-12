export function a(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) sum += v;
	return sum;
}

export * from "./external";
