// A tsconfig `paths` alias import, resolving to src/lib/shared.ts.
import { sharedFn } from "@lib/shared";

export function usesPathAlias(xs: number[]): number {
	return sharedFn(xs);
}

export { sharedFn };
