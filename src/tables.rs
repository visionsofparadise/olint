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

// ECMA-262 §23.1.3.30, §23.1.3.34, §23.2.3.29, §23.2.3.33: sort and toSorted reach
// SortIndexedProperties (§23.1.3.30.1), which calls SortCompare in an implementation-defined
// sequence, so each is an unknown contribution (spec §2.4).
pub static ARRAY_IMPLEMENTATION_DEFINED: &[&str] = &["sort", "toSorted"];

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
    "startsWith",
    "endsWith",
    "concat",
    "codePointAt",
];

// ECMA-262 §22.1.3.12, §22.1.3.15, §22.1.3.26-28, §22.1.3.30, §22.1.3.32-34: these delegate
// their work to host locale data or to Unicode algorithms rather than ECMAScript steps, so each
// is an unknown contribution (spec §2.4).
pub static STRING_IMPLEMENTATION_DEFINED: &[&str] = &[
    "localeCompare",
    "normalize",
    "toLocaleLowerCase",
    "toLocaleUpperCase",
    "toLowerCase",
    "toUpperCase",
    "trim",
    "trimStart",
    "trimEnd",
];

pub static REGEXP_LINEAR: &[&str] = &["test", "exec"];

pub static OBJECT_KEYED: &[&str] = &["keys", "values", "entries", "freeze", "assign"];

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
    ("WeakSet", Kind::WeakSet),
    ("Map", Kind::Map),
    ("ReadonlyMap", Kind::Map),
    ("WeakMap", Kind::WeakMap),
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

pub static REFLECTIVE_WRITES: &[&str] = &[
    "assign",
    "defineProperties",
    "defineProperty",
    "deleteProperty",
    "set",
    "setPrototypeOf",
];

pub fn method_matters(method: &str) -> bool {
    [
        ARRAY_LINEAR,
        ARRAY_IMPLEMENTATION_DEFINED,
        SET_LINEAR,
        MAP_LINEAR,
        STRING_LINEAR,
        STRING_IMPLEMENTATION_DEFINED,
        REGEXP_LINEAR,
    ]
    .iter()
    .any(|table| table.contains(&method))
}
