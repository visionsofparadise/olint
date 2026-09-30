//! The evaluation corpus members: every package in `corpus/.cache/packages.json`, the `model` and `tags`
//! regression fixtures, every dead-end fixture, every scaling family and the ceilings' instance families.

use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::families;

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

/// The member-id prefix of every package member.
const PACKAGES: &str = "packages/";

/// Whether a `--member` prefix can select a package member.
fn selects_packages(prefix: &str) -> bool {
    PACKAGES.starts_with(prefix) || prefix.starts_with(PACKAGES)
}

/// Lists the members of the olint tree at `tree` whose ids start with one of the `only` prefixes (all members when
/// `only` is empty), with packages taken from the corpus cache at `cache`. The package corpus is pinned, so a missing
/// `packages.json` is an error whenever the selection can include packages.
pub fn members(tree: &Path, cache: &Path, only: &[String]) -> Result<Vec<Member>, String> {
    let mut found = match only.is_empty() || only.iter().any(|prefix| selects_packages(prefix)) {
        true => packages(cache)?,
        false => Vec::new(),
    };

    found.extend(fixtures(tree)?);
    found.extend(family_members(cache)?);
    found.extend(ceilings(tree));
    found.retain(|member| {
        only.is_empty() || only.iter().any(|prefix| member.id.starts_with(prefix))
    });
    found.sort();

    Ok(found)
}

fn packages(cache: &Path) -> Result<Vec<Member>, String> {
    let path = cache.join("packages.json");
    let text = std::fs::read_to_string(&path).map_err(|error| {
        format!(
            "cannot read {}: {error}; run `npm run corpus` to build the pinned package corpus",
            path.display()
        )
    })?;
    let packages: Vec<Package> = serde_json::from_str(&text)
        .map_err(|error| format!("{} is malformed: {error}", path.display()))?;

    Ok(packages
        .into_iter()
        .map(|package| {
            let spec = format!("{}@{}", package.name, package.version);

            Member {
                id: format!("{PACKAGES}{spec}"),
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

/// The scaling families of `corpus/families/`, each generated into the cache at n = 2^`MEMBER_K`.
fn family_members(cache: &Path) -> Result<Vec<Member>, String> {
    let size = families::size_of(families::MEMBER_K);

    families::FAMILIES
        .iter()
        .map(|family| {
            Ok(Member {
                id: families::member_id(family.name),
                root: families::ensure(cache, family, size)?,
            })
        })
        .collect()
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
        let found = members(
            tree,
            &cache,
            &["fixtures/".to_string(), "families/".to_string()],
        )
        .expect("members list");

        assert!(members(tree, &cache, &[]).is_err());
        assert!(members(tree, &cache, &["packages/x".to_string()]).is_err());

        for name in FIXTURES {
            let member = found
                .iter()
                .find(|member| member.id == format!("fixtures/{name}"))
                .unwrap_or_else(|| panic!("fixtures/{name} is a member"));

            assert!(member.root.join("tsconfig.json").is_file());
        }

        for family in &families::FAMILIES {
            let member = found
                .iter()
                .find(|member| member.id == families::member_id(family.name))
                .unwrap_or_else(|| panic!("family {} is a member", family.name));

            assert!(member.root.join("src/index.ts").is_file());
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
