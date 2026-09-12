// A namespace import.
import * as star from "./star";

export interface NamedThing {
	value: number;
}

export function usesNamespaceImport(xs: number[]): number {
	return star.pkgWrapped(xs);
}
