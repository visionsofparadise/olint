//! Runs `scale` on the `flat` family at k = 6..=9 against the committed olint, and checks the recorded sizes, counts
//! and fits.

use std::path::Path;
use std::process::Command;

use serde_json::Value;

#[test]
fn flat_family_scales_at_small_sizes() {
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join(".cache/scale-test/flat.json");
    let output = Command::new(env!("CARGO_BIN_EXE_olint-corpus"))
        .args([
            "scale", "--src", "HEAD", "--family", "flat", "--min-k", "6", "--max-k", "9",
        ])
        .arg("--out")
        .arg(&out)
        .output()
        .expect("olint-corpus starts");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        output.status.success(),
        "scale failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let file: Value =
        serde_json::from_str(&std::fs::read_to_string(&out).expect("scale file")).expect("json");
    let passes = &file["families"]["flat"]["passes"];

    for pass in ["syntactic", "tsc"] {
        let scale = &passes[pass];
        let nodes: Vec<u64> = scale["sizes"]
            .as_array()
            .expect("sizes")
            .iter()
            .map(|size| size["nodes"].as_u64().expect("nodes"))
            .collect();

        assert_eq!(scale["max_k"], 9, "{pass}");
        assert_eq!(nodes.len(), 4, "{pass}");
        assert!(nodes.windows(2).all(|pair| pair[0] < pair[1]), "{pass}");
        assert_eq!(scale["metrics"]["nodes"]["order"], "n", "{pass}");
        assert_eq!(scale["metrics"]["WalkerNode"]["order"], "n", "{pass}");
        assert!(
            scale["metrics"]["peak_bytes"]["values"][0]
                .as_u64()
                .expect("peak")
                > 0,
            "{pass}"
        );
    }

    assert!(passes["tsc"]["metrics"]["tsc.programs"].is_object());
    assert!(stdout.contains("flat syntactic: max k 9"), "{stdout}");
}
