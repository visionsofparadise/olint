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

// A costed callback substituted into a callback parameter, itself called
// inside a loop: the caller's cost reflects the callback's real cost.
export function callbackSubstituted(n: number): number {
	return runNTimes(n, costedCallback);
}

function sumRest(...args: number[]): number {
	return args.reduce((a, b) => a + b, 0);
}

// A rest parameter spread at a call site, wrapped in a real loop so the
// spread's cost shows up in the printed chain.
export function spreadAtCallSite(rows: number[][]): number {
	let total = 0;
	for (const xs of rows) total += sumRest(...xs);
	return total;
}

// An inline callback passed directly to a call.
export function inlineCallbackCall(xs: number[]): number[] {
	return xs.map((v) => v * 2);
}

function makeAdder(base: number): (x: number) => number {
	return (x: number) => x + base;
}

// A function that returns another function.
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

// A call made through an `as` cast on the callee.
export function callThroughCast(x: number): number {
	return (calleeFn as CalleeType)(x);
}
