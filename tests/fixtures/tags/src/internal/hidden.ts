export function hidden(xs: number[][]): number {
	let sum = 0;
	for (const row of xs) for (const v of row) for (const w of row) for (const z of row) sum += v * w * z;
	return sum;
}
