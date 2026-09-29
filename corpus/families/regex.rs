//! n exported functions, each applying its own regex literal; the literals cycle through four shapes, one of them with
//! nested quantifiers.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    index(lines((0..size).map(|i| match i % 4 {
        0 => format!(
            "export function m{i}(s: string): boolean {{ return /^k{i}_(?:b|c)+$/.test(s); }}"
        ),
        1 => format!(
            "export function m{i}(s: string): string {{ return s.replace(/k{i}[a-z]*/g, \"\"); }}"
        ),
        2 => {
            format!("export function m{i}(s: string): boolean {{ return /(?:a+)+k{i}/.test(s); }}")
        }
        _ => {
            format!("export function m{i}(s: string): string[] {{ return s.split(/[,;]k{i} */); }}")
        }
    })))
}
