//! n modules: module `m{i}` imports `f{(i-1)/2}` from its parent along a binary tree and exports `f{i}`, and
//! `src/index.ts` re-exports every `f{i}`.

use super::{lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    let mut files: Vec<Source> = (0..size)
        .map(|i| {
            let text = match i {
                0 => "export function f0(xs: number[]): number { let total = 0; for (const x of xs) { total += x; } return total; }\n".to_string(),
                _ => {
                    let parent = (i - 1) / 2;

                    format!(
                        "import {{ f{parent} }} from \"./m{parent}\";\nexport function f{i}(xs: number[]): number {{ return f{parent}(xs) + {i}; }}\n"
                    )
                }
            };

            (format!("src/m{i}.ts"), text)
        })
        .collect();

    files.push((
        "src/index.ts".to_string(),
        lines((0..size).map(|i| format!("export {{ f{i} }} from \"./m{i}\";"))),
    ));

    files
}
