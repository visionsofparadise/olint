use crate::declared_types::Kind;

pub static ARRAY_LINEAR: &[&str] = &[
    "includes",
    "indexOf",
    "lastIndexOf",
    "find",
    "findIndex",
    "findLast",
    "findLastIndex",
    "some",
    "every",
    "filter",
    "map",
    "forEach",
    "reduce",
    "reduceRight",
    "flat",
    "flatMap",
    "concat",
    "slice",
    "splice",
    "shift",
    "unshift",
    "join",
    "reverse",
    "fill",
    "copyWithin",
    "toReversed",
    "toSpliced",
    "with",
    "set",
];

pub static ARRAY_N_LOG_N: &[&str] = &["sort", "toSorted"];

pub static CALLBACK_METHODS: &[&str] = &[
    "forEach",
    "map",
    "filter",
    "reduce",
    "reduceRight",
    "some",
    "every",
    "find",
    "findIndex",
    "findLast",
    "findLastIndex",
    "flatMap",
    "sort",
    "toSorted",
];

pub static SET_LINEAR: &[&str] = &[
    "forEach",
    "union",
    "intersection",
    "difference",
    "symmetricDifference",
    "isSubsetOf",
    "isSupersetOf",
    "isDisjointFrom",
];

pub static MAP_LINEAR: &[&str] = &["forEach"];

pub static STRING_LINEAR: &[&str] = &[
    "includes",
    "indexOf",
    "lastIndexOf",
    "split",
    "replace",
    "replaceAll",
    "match",
    "matchAll",
    "search",
    "slice",
    "substring",
    "substr",
    "repeat",
    "padStart",
    "padEnd",
    "trim",
    "trimStart",
    "trimEnd",
    "toLowerCase",
    "toUpperCase",
    "toLocaleLowerCase",
    "toLocaleUpperCase",
    "normalize",
    "localeCompare",
    "startsWith",
    "endsWith",
    "concat",
    "codePointAt",
];

pub static REGEXP_LINEAR: &[&str] = &["test", "exec"];

pub static GLOBAL_LINEAR: &[(&str, &[&str])] = &[
    ("Array", &["from", "of"]),
    (
        "Object",
        &[
            "keys",
            "values",
            "entries",
            "assign",
            "fromEntries",
            "freeze",
            "groupBy",
        ],
    ),
    ("JSON", &["parse", "stringify"]),
    (
        "Buffer",
        &["from", "concat", "alloc", "allocUnsafe", "compare"],
    ),
    ("Map", &["groupBy"]),
];

pub static OBJECT_KEYED: &[&str] = &["keys", "values", "entries", "freeze", "assign"];

pub static GLOBAL_FUNCTIONS_LINEAR: &[&str] = &["structuredClone"];

pub static LINEAR_CONSTRUCTORS: &[&str] = &[
    "Set",
    "Map",
    "WeakSet",
    "WeakMap",
    "Array",
    "Int8Array",
    "Uint8Array",
    "Uint8ClampedArray",
    "Int16Array",
    "Uint16Array",
    "Int32Array",
    "Uint32Array",
    "Float32Array",
    "Float64Array",
    "BigInt64Array",
    "BigUint64Array",
    "ArrayBuffer",
    "SharedArrayBuffer",
    "DataView",
];

pub static TYPED_ARRAYS: &[&str] = &[
    "Int8Array",
    "Uint8Array",
    "Uint8ClampedArray",
    "Int16Array",
    "Uint16Array",
    "Int32Array",
    "Uint32Array",
    "Float32Array",
    "Float64Array",
    "BigInt64Array",
    "BigUint64Array",
];

pub static KIND_OF_NAME: &[(&str, Kind)] = &[
    ("Array", Kind::Array),
    ("ReadonlyArray", Kind::Array),
    ("Set", Kind::Set),
    ("ReadonlySet", Kind::Set),
    ("WeakSet", Kind::Set),
    ("Map", Kind::Map),
    ("ReadonlyMap", Kind::Map),
    ("WeakMap", Kind::Map),
    ("String", Kind::String),
    ("RegExp", Kind::RegExp),
];

pub static STRING_TO_ARRAY: &[&str] = &["split", "match"];

pub static ARRAY_TO_ARRAY: &[&str] = &[
    "map",
    "filter",
    "slice",
    "concat",
    "flat",
    "flatMap",
    "sort",
    "toSorted",
    "reverse",
    "toReversed",
    "with",
    "toSpliced",
    "splice",
    "fill",
];

pub static DERIVED_METHODS: &[&str] = &[
    "map",
    "filter",
    "slice",
    "concat",
    "sort",
    "toSorted",
    "reverse",
    "toReversed",
    "with",
    "toSpliced",
    "flatMap",
];

pub static MUTATORS: &[&str] = &[
    "add",
    "set",
    "push",
    "unshift",
    "delete",
    "clear",
    "pop",
    "shift",
    "splice",
    "sort",
    "reverse",
    "fill",
    "copyWithin",
];

pub fn method_matters(method: &str) -> bool {
    [
        ARRAY_LINEAR,
        ARRAY_N_LOG_N,
        SET_LINEAR,
        MAP_LINEAR,
        STRING_LINEAR,
        REGEXP_LINEAR,
    ]
    .iter()
    .any(|table| table.contains(&method))
}
