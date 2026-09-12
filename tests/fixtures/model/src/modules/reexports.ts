// Named re-export with a rename.
export { a as b } from "./star";

// A default export, re-exported through src/index.ts.
export default function reexportDefault(rows: number[][]): number {
	let sum = 0;
	for (const row of rows) for (const v of row) sum += v * 2;
	return sum;
}
