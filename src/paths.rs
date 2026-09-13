use std::path::{Component, Path, PathBuf};

pub fn canonical_path_of(path: &Path) -> std::io::Result<PathBuf> {
    std::fs::canonicalize(path).map(|canonical| strip_verbatim_prefix(&canonical))
}

pub fn forward_slashes_of(path: impl AsRef<Path>) -> String {
    path.as_ref().to_string_lossy().replace('\\', "/")
}

pub(crate) fn strip_verbatim_prefix(path: &Path) -> PathBuf {
    let text = path.to_string_lossy();

    if let Some(rest) = text.strip_prefix(r"\\?\UNC\") {
        return PathBuf::from(format!(r"\\{rest}"));
    }

    if let Some(rest) = text.strip_prefix(r"\\?\") {
        return PathBuf::from(rest);
    }

    path.to_path_buf()
}

pub fn relative_path_of(root: &Path, path: &Path) -> String {
    let root_components: Vec<Component> = root.components().collect();
    let path_components: Vec<Component> = path.components().collect();
    let shared = root_components
        .iter()
        .zip(&path_components)
        .take_while(|(left, right)| left == right)
        .count();
    let mut segments: Vec<String> = vec!["..".to_string(); root_components.len() - shared];

    segments.extend(
        path_components[shared..]
            .iter()
            .map(|component| component.as_os_str().to_string_lossy().into_owned()),
    );

    segments.join("/")
}

pub fn normalized_path_of(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();

    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }

    normalized
}
