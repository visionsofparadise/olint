//! One strongly connected component of n mutually recursive functions: `r{i}` reads index `i` of its input and calls
//! `r{i+1 mod n}` with the next index, so the cycle advances one element per call.

use super::{functions, Source};

pub fn generate(size: usize) -> Vec<Source> {
    functions(size, |i, export| {
        format!(
            "{export}function r{i}(xs: number[], at: number): number {{ return at >= xs.length ? 0 : xs[at] + r{}(xs, at + 1); }}",
            (i + 1) % size
        )
    })
}
