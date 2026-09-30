//! The scaling families: generators of TypeScript programs indexed by a size n = 2^k, which `scale` analyses at
//! k = `Family::min_k..=MAX_K` to measure how olint's work and memory grow (spec §7.5).
//!
//! Each family writes its program into `corpus/.cache/families/<family>/<n>/` with a `tsconfig.json` and an
//! `olint.config.json` whose entrypoint is `src/index.ts`. The programs are analysed and never executed. Every family is
//! also an evaluation corpus member at n = 2^`MEMBER_K`.

mod chains;
mod files;
mod flat;
mod generics;
mod nesting;
mod objects;
mod recursion;
mod regex;
mod switch;

use std::path::{Path, PathBuf};

/// The smallest k of a family whose work limits and failures begin late enough to leave `scale::MINIMUM_POINTS`
/// sizes from there.
pub const MIN_K: u32 = 6;
pub const MAX_K: u32 = 14;
/// The size at which each family is an evaluation corpus member.
pub const MEMBER_K: u32 = 8;

/// One generated source file: its path under the family root and its text.
pub type Source = (String, String);

pub struct Family {
    pub name: &'static str,
    /// What the size n counts.
    pub shape: &'static str,
    pub generate: fn(usize) -> Vec<Source>,
    /// The smallest k `scale` runs, low enough that `scale::MINIMUM_POINTS` sizes run before the family first reads a
    /// scheduler work limit or fails.
    pub min_k: u32,
}

pub const FAMILIES: [Family; 9] = [
    Family {
        name: "flat",
        shape: "n independent exported functions, each with one loop",
        generate: flat::generate,
        min_k: MIN_K,
    },
    Family {
        name: "chains",
        shape: "one call chain of n functions",
        generate: chains::generate,
        // Every function is a root, so the chain's task keys grow as n^2 and reach their limit at k=8.
        min_k: 3,
    },
    Family {
        name: "nesting",
        shape: "one function whose if statements nest n deep",
        generate: nesting::generate,
        // k=8 overflows the member process's stack.
        min_k: 3,
    },
    Family {
        name: "objects",
        shape: "one object literal with n function-valued properties, read by key and iterated",
        generate: objects::generate,
        min_k: MIN_K,
    },
    Family {
        name: "switch",
        shape: "one switch with n cases, each with one loop",
        generate: switch::generate,
        min_k: MIN_K,
    },
    Family {
        name: "recursion",
        shape: "one strongly connected component of n mutually recursive functions",
        generate: recursion::generate,
        // Recurrence contexts grow as n^3 and reach their limit at k=4.
        min_k: 0,
    },
    Family {
        name: "regex",
        shape: "n functions, each testing or replacing with its own regex literal",
        generate: regex::generate,
        min_k: MIN_K,
    },
    Family {
        name: "generics",
        shape: "n generic functions over generic interfaces, each chaining array methods on a type parameter",
        generate: generics::generate,
        min_k: MIN_K,
    },
    Family {
        name: "files",
        shape: "n modules importing along a binary tree, re-exported from one index",
        generate: files::generate,
        min_k: MIN_K,
    },
];

const TSCONFIG: &str = r#"{
	"compilerOptions": {
		"target": "ES2022",
		"module": "ESNext",
		"moduleResolution": "bundler",
		"strict": true,
		"lib": ["ES2022"],
		"noEmit": true
	},
	"include": ["src/**/*.ts"]
}
"#;

const CONFIG: &str = r#"{
	"entrypoints": ["src/index.ts"]
}
"#;

/// The stamp file recording a generated directory's content hash, so regeneration writes only when a generator changed.
const STAMP: &str = ".generated";

pub fn family(name: &str) -> Option<&'static Family> {
    FAMILIES.iter().find(|family| family.name == name)
}

pub fn size_of(k: u32) -> usize {
    1 << k
}

/// The member identifier of a family at size n.
pub fn member_id(name: &str) -> String {
    format!("families/{name}")
}

pub fn directory(cache: &Path, name: &str, size: usize) -> PathBuf {
    cache.join("families").join(name).join(size.to_string())
}

/// The full file set of a family at size n: its sources plus the generated project files.
pub fn files_of(family: &Family, size: usize) -> Vec<Source> {
    let mut files = (family.generate)(size);

    files.push(("tsconfig.json".to_string(), TSCONFIG.to_string()));
    files.push(("olint.config.json".to_string(), CONFIG.to_string()));
    files.sort();

    files
}

/// FNV-1a over every path and text, as the stamp of a generated directory.
fn fingerprint(files: &[Source]) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;

    for (path, text) in files {
        for byte in path.bytes().chain([0]).chain(text.bytes()).chain([0]) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0100_0000_01b3);
        }
    }

    format!("{hash:016x} {}\n", files.len())
}

/// Writes the family at size n into the cache unless its stamp shows the same content, and returns its root.
pub fn ensure(cache: &Path, family: &Family, size: usize) -> Result<PathBuf, String> {
    let root = directory(cache, family.name, size);
    let files = files_of(family, size);
    let stamp = fingerprint(&files);
    let stamp_path = root.join(STAMP);

    if std::fs::read_to_string(&stamp_path).is_ok_and(|text| text == stamp) {
        return Ok(root);
    }

    for (path, text) in &files {
        let target = root.join(path);
        let parent = target.parent().expect("generated files have a parent");

        std::fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
        std::fs::write(&target, text)
            .map_err(|error| format!("cannot write {}: {error}", target.display()))?;
    }

    std::fs::write(&stamp_path, stamp)
        .map_err(|error| format!("cannot write {}: {error}", stamp_path.display()))?;

    Ok(root)
}

/// Joins generated lines into one source text ending in a newline.
fn lines(lines: impl IntoIterator<Item = String>) -> String {
    let mut text = lines.into_iter().collect::<Vec<_>>().join("\n");

    text.push('\n');

    text
}

fn index(text: String) -> Vec<Source> {
    vec![("src/index.ts".to_string(), text)]
}

/// One `src/index.ts` of n functions, the first exported; `function` writes function `i` after its export prefix.
fn functions(size: usize, function: impl Fn(usize, &str) -> String) -> Vec<Source> {
    index(lines(
        (0..size).map(|i| function(i, if i == 0 { "export " } else { "" })),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn families_are_deterministic_and_grow_with_n() {
        for family in &FAMILIES {
            let small = files_of(family, 64);
            let large = files_of(family, 128);

            assert_eq!(small, files_of(family, 64), "{}", family.name);

            let bytes = |files: &[Source]| files.iter().map(|(_, text)| text.len()).sum::<usize>();

            assert!(bytes(&large) > bytes(&small), "{}", family.name);
            assert!(
                small.iter().any(|(path, _)| path == "src/index.ts"),
                "{}",
                family.name
            );
            assert!(
                small.iter().all(|(_, text)| !text.contains('\r')),
                "{}",
                family.name
            );
        }
    }

    #[test]
    fn names_are_unique() {
        for (index, family) in FAMILIES.iter().enumerate() {
            assert!(FAMILIES[..index]
                .iter()
                .all(|other| other.name != family.name));
        }
    }
}
