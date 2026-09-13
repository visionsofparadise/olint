use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use serde::{Deserialize, Serialize};

use crate::declared_types::Kind;

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "query", rename_all = "lowercase")]
pub enum Query {
    Type { file: String, pos: u32, end: u32 },
    Callee { file: String, pos: u32, end: u32 },
}

#[derive(Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeAnswer {
    pub kind: Kind,
    pub tuple: bool,
    pub closed: bool,
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CalleeAnswer {
    pub file: String,
    pub start: u32,
    pub end: u32,
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "query", rename_all = "lowercase")]
pub enum OracleAnswer {
    Type(TypeAnswer),
    Callee(CalleeAnswer),
}

#[derive(Deserialize, Debug)]
pub struct OracleReply {
    pub typescript: String,
    pub from: String,
    pub answers: Vec<Option<OracleAnswer>>,
}

#[derive(Debug)]
pub enum OracleError {
    NodeUnavailable(std::io::Error),
    TypescriptUnavailable(String),
    Failed { status: Option<i32>, stderr: String },
    Malformed(String),
}

#[derive(Serialize)]
struct Request<'q> {
    tsconfig: String,
    queries: &'q [Query],
}

pub const SCRIPT: &str = include_str!("types_oracle.mjs");

const TYPESCRIPT_UNAVAILABLE: i32 = 3;

pub fn ask(root: &Path, tsconfig: &Path, queries: &[Query]) -> Result<OracleReply, OracleError> {
    let tsconfig = std::path::absolute(tsconfig).map_err(OracleError::NodeUnavailable)?;
    let request = serde_json::to_vec(&Request {
        tsconfig: tsconfig.to_string_lossy().into_owned(),
        queries,
    })
    .map_err(|error| OracleError::Malformed(error.to_string()))?;
    let mut child = Command::new("node")
        .args(["--input-type=module", "--eval", SCRIPT])
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(OracleError::NodeUnavailable)?;
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let writer = std::thread::spawn(move || stdin.write_all(&request));
    let output = child
        .wait_with_output()
        .map_err(OracleError::NodeUnavailable)?;
    let _ = writer.join();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    match output.status.code() {
        Some(0) => serde_json::from_slice(&output.stdout)
            .map_err(|error| OracleError::Malformed(error.to_string())),
        Some(TYPESCRIPT_UNAVAILABLE) => Err(OracleError::TypescriptUnavailable(stderr)),
        status => Err(OracleError::Failed { status, stderr }),
    }
}
