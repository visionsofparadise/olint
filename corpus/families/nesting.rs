//! One exported function whose `if` statements nest n deep, each level adding one and guarding the next.

use super::{index, Source};

pub fn generate(size: usize) -> Vec<Source> {
    let mut text = String::from("export function deep(xs: number[]): number {\n\tlet total = 0;\n");

    for i in 0..size {
        text.push_str(&format!("if (xs.length > {i}) {{ total += xs[{i}]; "));
    }

    text.push_str(&"}".repeat(size));
    text.push_str("\n\treturn total;\n}\n");

    index(text)
}
