//! n independent exported functions, each summing its input in one loop.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    index(lines((0..size).map(|i| {
        format!(
            "export function f{i}(xs: number[]): number {{ let total = {i}; for (const x of xs) {{ total += x; }} return total; }}"
        )
    })))
}
