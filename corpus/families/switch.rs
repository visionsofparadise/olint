//! One exported function whose switch has n cases, each looping over the input once.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    let mut text = vec![
        "export function pick(code: number, xs: number[]): number {".to_string(),
        "\tswitch (code) {".to_string(),
    ];

    text.extend((0..size).map(|i| {
        format!("\t\tcase {i}: {{ let total = 0; for (const x of xs) {{ total += x * {i}; }} return total; }}")
    }));
    text.push("\t\tdefault: return -1;".to_string());
    text.push("\t}".to_string());
    text.push("}".to_string());

    index(lines(text))
}
