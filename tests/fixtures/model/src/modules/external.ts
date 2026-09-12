import { pkgFn } from "pkg";

export function pkgWrapped(xs: number[]): number {
	return pkgFn(xs);
}
