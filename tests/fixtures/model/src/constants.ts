// Array literal with a constant spread.
export function arrayLiteralSpread(): number {
	const xs = [...[1, 2, 3], 4];
	return xs.length;
}

// Conditional expression of two constants.
export function conditionalConstants(flag: boolean): number[] {
	return flag ? [1, 2, 3] : [4, 5];
}

// map/filter/flatMap/concat of a constant-sized array.
export function derivedConstantArrays(): number {
	const xs = [1, 2, 3];
	return (
		xs.map((v) => v * 2).length +
		xs.filter((v) => v > 0).length +
		xs.flatMap((v) => [v, v]).length +
		xs.concat([4, 5]).length
	);
}

// new Array(<constant>).
export function newArrayConstant(): number[] {
	return new Array(4);
}

class SizedConst {
	readonly size: number = 8;
	values(): number[] {
		return new Array(this.size);
	}
}

// readonly class field with a constant initializer.
export function readonlyFieldConst(): number[] {
	return new SizedConst().values();
}

const enum Color {
	Red,
	Green,
	Blue,
}

// const enum used with Object.keys.
export function constEnumKeys(): string[] {
	return Object.keys(Color);
}

// as const.
export function asConstArray() {
	return [1, 2, 3] as const;
}

// string literal (constant-sized as a string).
export function stringLiteralConstant(): string {
	return "a constant string literal";
}
