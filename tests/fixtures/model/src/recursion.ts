function factorialLike(n: number): number {
	return n <= 0 ? 1 : n * factorialLike(n - 1);
}
export function directRecursion(n: number): number {
	return factorialLike(n);
}

function isEvenRec(n: number): boolean {
	return n === 0 ? true : isOddRec(n - 1);
}
function isOddRec(n: number): boolean {
	return n === 0 ? false : isEvenRec(n - 1);
}
export function mutualRecursionCaller(n: number): boolean {
	return isEvenRec(n);
}

function cycleStart(n: number, xs: number[]): number {
	if (n <= 0) return 0;
	return new CycleHolder().step(n - 1, xs);
}
class CycleHolder {
	step(n: number, xs: number[]): number {
		if (n <= 0) return 0;
		return cycleContinue(n - 1, xs) + xs.length;
	}
}
function cycleContinue(n: number, xs: number[]): number {
	if (n <= 0) return 0;
	return cycleStart(n - 1, xs);
}
export function threeCycleEntry(n: number, matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) sum += cycleStart(n, row);
	return sum;
}

export function callsCycleMemberDirectly(n: number, matrix: number[][]): number {
	let sum = 0;
	for (const row of matrix) sum += new CycleHolder().step(n, row);
	return sum;
}
