export class CostedCtor {
	total: number;
	constructor(rows: number[][]) {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		this.total = sum;
	}
}
export function instantiateCostedCtor(rows: number[][]): number {
	return new CostedCtor(rows).total;
}

export class WithPrivateMethod {
	private compute(rows: number[][]): number {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		return sum;
	}
	run(rows: number[][]): number {
		return this.compute(rows);
	}
}
export function callsPrivateMethod(rows: number[][]): number {
	return new WithPrivateMethod().run(rows);
}

export class WithHashPrivateMethod {
	#compute(rows: number[][]): number {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		return sum;
	}
	run(rows: number[][]): number {
		return this.#compute(rows);
	}
}
export function callsHashPrivateMethod(rows: number[][]): number {
	return new WithHashPrivateMethod().run(rows);
}

export class WithGetter {
	constructor(private rows: number[][]) {}
	get total(): number {
		let sum = 0;
		for (const row of this.rows) for (const v of row) sum += v;
		return sum;
	}
}
export function readsGetter(rows: number[][]): number {
	return new WithGetter(rows).total;
}

export class WithStaticMethod {
	static compute(rows: number[][]): number {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		return sum;
	}
}
export function callsStaticMethod(rows: number[][]): number {
	return WithStaticMethod.compute(rows);
}

export class WithArrowProperty {
	handler = (rows: number[][]): number => {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		return sum;
	};
}
export function callsArrowProperty(rows: number[][]): number {
	return new WithArrowProperty().handler(rows);
}

export class WithReadonlyItems {
	readonly items: number[] = [];
	addAll(xs: number[]): void {
		this.items.push(...xs);
	}
}
export function pushesToReadonlyItems(xs: number[]): number {
	const c = new WithReadonlyItems();
	c.addAll(xs);
	return c.items.length;
}

export const ClassExpressionExample = class {
	run(rows: number[][]): number {
		let sum = 0;
		for (const row of rows) for (const v of row) sum += v;
		return sum;
	}
};
export function usesClassExpression(rows: number[][]): number {
	return new ClassExpressionExample().run(rows);
}

declare const mergedItems: number[];

interface MergedHolder {
	run(): number;
}

class MergedHolder {
	run(): number {
		return mergedItems.indexOf(1);
	}
	self(): number {
		return this.run();
	}
}

export function useMergedHolder(): number {
	return new MergedHolder().self();
}

export class ComputedKeys {
	[ Symbol.iterator ]() {
		return [1].values();
	}
}

interface QuotedHolder {
	"run"(): number;
}

class QuotedHolder {
	run(): number {
		return mergedItems.indexOf(2);
	}
	self(): number {
		return this.run();
	}
}

export function useQuotedHolder(): number {
	return new QuotedHolder().self();
}
