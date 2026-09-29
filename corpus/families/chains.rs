//! One call chain of n functions: the exported `f0` calls `f1`, and so on, and the last one loops over its input.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    index(lines((0..size).map(|i| {
        let export = if i == 0 { "export " } else { "" };

        match i + 1 == size {
            true => format!(
                "{export}function f{i}(xs: number[]): number {{ let total = 0; for (const x of xs) {{ total += x; }} return total; }}"
            ),
            false => format!(
                "{export}function f{i}(xs: number[]): number {{ return f{}(xs) + {i}; }}",
                i + 1
            ),
        }
    })))
}
