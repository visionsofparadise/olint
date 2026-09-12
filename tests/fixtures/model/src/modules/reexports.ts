export { a as b } from "./star";

export default function reexportDefault(rows: number[][]): number {
	let sum = 0;
	for (const row of rows) for (const v of row) sum += v * 2;
	return sum;
}
