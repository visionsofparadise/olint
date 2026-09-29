//! The evaluation corpus members: every package in `corpus/.cache/packages.json`, the `model` and `tags`
//! regression fixtures, every dead-end fixture, every scaling family and the ceilings' instance families.

use std::path::{Path, PathBuf};

use serde::Deserialize;

pub const FIXTURES: [&str; 2] = ["model", "tags"];

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Member {
    /// Stable identifier, also the member's relative path inside a snapshot directory.
    pub id: String,
    /// Directory holding the member's `tsconfig.json`.
    pub root: PathBuf,
}

#[derive(Deserialize)]
struct Package {
    name: String,
    version: String,
}

/// Lists the members of the olint tree at `tree`, with packages taken from the corpus cache at `cache`.
pub fn members(tree: &Path, cache: &Path) -> Result<Vec<Member>, String> {
    let mut found = packages(cache)?;

    found.extend(fixtures(tree)?);
    found.extend(families(tree));
    found.extend(ceilings(tree));
    found.sort();

    Ok(found)
}

fn packages(cache: &Path) -> Result<Vec<Member>, String> {
    let path = cache.join("packages.json");
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(format!("cannot read {}: {error}", path.display())),
    };
    let packages: Vec<Package> = serde_json::from_str(&text)
        .map_err(|error| format!("{} is malformed: {error}", path.display()))?;

    Ok(packages
        .into_iter()
        .map(|package| {
            let spec = format!("{}@{}", package.name, package.version);

            Member {
                id: format!("packages/{spec}"),
                root: cache.join("packages").join(&spec),
            }
        })
        .collect())
}

fn fixtures(tree: &Path) -> Result<Vec<Member>, String> {
    let directory = tree.join("tests/fixtures");
    let mut found: Vec<Member> = FIXTURES
        .iter()
        .map(|name| Member {
            id: format!("fixtures/{name}"),
            root: directory.join(name),
        })
        .collect();
    let dead_ends = directory.join("dead-ends");

    if dead_ends.is_dir() {
        let entries = std::fs::read_dir(&dead_ends)
            .map_err(|error| format!("cannot list {}: {error}", dead_ends.display()))?;

        for entry in entries {
            let entry =
                entry.map_err(|error| format!("cannot list {}: {error}", dead_ends.display()))?;

            if entry.path().is_dir() {
                found.push(Member {
                    id: format!("dead-ends/{}", entry.file_name().to_string_lossy()),
                    root: entry.path(),
                });
            }
        }
    }

    Ok(found)
}

/// The scaling families of `corpus/families/`, which action 1.4 adds.
fn families(_tree: &Path) -> Vec<Member> {
    Vec::new()
}

/// The instance families of `proofs/Olint/Ceilings/`, which action 7.3 adds.
fn ceilings(_tree: &Path) -> Vec<Member> {
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repository_members_include_the_regression_fixtures() {
        let corpus = Path::new(env!("CARGO_MANIFEST_DIR"));
        let tree = corpus
            .parent()
            .expect("the corpus package sits in the olint tree");
        let cache = corpus.join(".cache/absent-for-tests");
        let found = members(tree, &cache).expect("members list");

        for name in FIXTURES {
            let member = found
                .iter()
                .find(|member| member.id == format!("fixtures/{name}"))
                .unwrap_or_else(|| panic!("fixtures/{name} is a member"));

            assert!(member.root.join("tsconfig.json").is_file());
        }

        assert!(found.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn packages_resolve_under_the_cache() {
        let directory =
            std::env::temp_dir().join(format!("olint-corpus-members-{}", std::process::id()));

        std::fs::create_dir_all(&directory).expect("directory");
        std::fs::write(
            directory.join("packages.json"),
            r#"[{ "name": "@scope/pkg", "version": "1.2.3", "integrity": "sha512-x", "tarball": "t" }]"#,
        )
        .expect("packages.json");

        let found = packages(&directory).expect("packages");

        std::fs::remove_dir_all(&directory).expect("cleanup");
        assert_eq!(
            found,
            vec![Member {
                id: "packages/@scope/pkg@1.2.3".to_string(),
                root: directory.join("packages").join("@scope/pkg@1.2.3"),
            }]
        );
    }
}
