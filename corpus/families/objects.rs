//! One object literal with n function-valued properties, read by a computed key and iterated with `Object.values`.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    let mut text = vec!["const table = {".to_string()];

    text.extend((0..size).map(|i| format!("\tk{i}: (xs: number[]): number => xs.length + {i},")));
    text.push("};".to_string());
    text.push(
        "export function lookup(key: keyof typeof table, xs: number[]): number { return table[key](xs); }".to_string(),
    );
    text.push(
        "export function sum(xs: number[]): number { let total = 0; for (const f of Object.values(table)) { total += f(xs); } return total; }"
            .to_string(),
    );

    index(lines(text))
}
