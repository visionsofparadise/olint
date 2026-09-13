function costedCallback(x: number): number {
	let sum = 0;
	for (let i = 0; i < x; i++) sum += i;
	return sum;
}

function runNTimes(n: number, cb: (i: number) => number): number {
	let sum = 0;
	for (let i = 0; i < n; i++) sum += cb(i);
	return sum;
}

export function callbackSubstituted(n: number): number {
	return runNTimes(n, costedCallback);
}

function sumRest(...args: number[]): number {
	return args.reduce((a, b) => a + b, 0);
}

export function spreadAtCallSite(rows: number[][]): number {
	let total = 0;
	for (const xs of rows) total += sumRest(...xs);
	return total;
}

export function inlineCallbackCall(xs: number[]): number[] {
	return xs.map((v) => v * 2);
}

function makeAdder(base: number): (x: number) => number {
	return (x: number) => x + base;
}

export function functionReturningFunction(base: number, xs: number[]): number[] {
	const adder = makeAdder(base);
	return xs.map(adder);
}

function calleeFn(x: number): number {
	let sum = 0;
	for (let i = 0; i < x; i++) sum += i;
	return sum;
}

type CalleeType = (x: number) => number;

export function callThroughCast(x: number): number {
	return (calleeFn as CalleeType)(x);
}

export function destructureRest(xs: number[]): number {
	let head: number;
	let rest: number[];
	[head, ...rest] = xs;
	return head + rest.length;
}

export function destructureObjectRest(obj: Record<string, number>): Record<string, number> {
	let rest: Record<string, number>;
	({ ...rest } = obj);
	return rest;
}

function makeIdentity(xs: number[]) {
	return xs.map((x) => x);
}

export function instantiationExpression(xs: number[]) {
	const g = makeIdentity(xs)<number>;
	return g;
}
