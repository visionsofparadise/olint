use super::lines_of_chain;
use crate::cost::{Cost, Factor};
use crate::project::{FileId, Site};

fn factor_of(label: &str, line: u32, cost: Cost, inner: Vec<Factor>) -> Factor {
    Factor {
        label: label.to_string(),
        site: Site {
            file: FileId(0),
            line,
        },
        cost,
        inner,
    }
}

#[test]
fn chains_pad_labels_and_nest_inner_calls() {
    let chain = vec![
        factor_of("for-of", 137, Cost::N, Vec::new()),
        factor_of(
            "call costFn()",
            137,
            Cost::N,
            vec![factor_of("@perf O(N)", 129, Cost::N, Vec::new())],
        ),
    ];
    let mut out = Vec::new();

    lines_of_chain(&chain, 1, &mut out, &|site| {
        format!("src/tags.ts:{}", site.line)
    });

    assert_eq!(
        out,
        vec![
            "    in loop for-of                                           src/tags.ts:137  x N",
            "        calls costFn()                                     src/tags.ts:137  = O(N)",
            "        reads as @perf O(N)                                   src/tags.ts:129  = O(N)",
        ]
    );
}
