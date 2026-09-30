//! One call chain of n functions: the exported `f0` calls `f1`, and so on, and the last one loops over its input.

use super::{functions, Source};

pub fn generate(size: usize) -> Vec<Source> {
    functions(size, |i, export| {
        match i + 1 == size {
        true => format!(
            "{export}function f{i}(xs: number[]): number {{ let total = 0; for (const x of xs) {{ total += x; }} return total; }}"
        ),
        false => format!(
            "{export}function f{i}(xs: number[]): number {{ return f{}(xs) + {i}; }}",
            i + 1
        ),
    }
    })
}
