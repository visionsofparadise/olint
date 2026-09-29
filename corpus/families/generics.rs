//! n exported generic functions over generic interfaces: each maps, filters and reduces an array of a type-parameter
//! box through a fixed-depth alias chain, so every array method call is a checker query on a generic receiver.

use super::{index, lines, Source};

pub fn generate(size: usize) -> Vec<Source> {
    let mut text = vec![
        "interface Box<T> { readonly value: T; readonly items: readonly T[] }".to_string(),
        "type Pair<T> = Box<[T, T]>;".to_string(),
        "type Nest<T> = Box<Pair<T>>;".to_string(),
    ];

    text.extend((0..size).map(|i| {
        format!(
            "export function g{i}<T extends {{ length: number }}>(boxes: Nest<T>[]): number {{ return boxes.map((box) => box.value.value[0].length).filter((length) => length > {i}).reduce((total, length) => total + length, 0); }}"
        )
    }));

    index(lines(text))
}
