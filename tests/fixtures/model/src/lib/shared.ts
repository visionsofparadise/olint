export function sharedFn(xs: number[]): number {
	return xs.sort((a, b) => a - b).length;
}
