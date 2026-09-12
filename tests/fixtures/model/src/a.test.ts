export function quarticTestFn(matrix: number[][]): number {
	let sum = 0;
	for (const a of matrix) for (const b of matrix) for (const c of matrix) for (const d of matrix) sum += a.length + b.length + c.length + d.length;
	return sum;
}
