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
    pub structural: bool,
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CalleeTarget {
    pub file: String,
    pub start: u32,
    pub end: u32,
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CalleeAnswer {
    pub targets: Vec<CalleeTarget>,
    pub open: bool,
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "query", rename_all = "lowercase")]
pub enum TscAnswer {
    Type(TypeAnswer),
    Callee(CalleeAnswer),
}

#[derive(Debug)]
pub struct TscReply {
    pub typescript: String,
    pub from: String,
    pub answers: Vec<Option<TscAnswer>>,
}

#[derive(Debug)]
pub enum TscError {
    NodeUnavailable(std::io::Error),
    TypescriptUnavailable(String),
    Failed { status: Option<i32>, stderr: String },
    Malformed(String),
}

pub const PROTOCOL_VERSION: u32 = 2;

#[derive(Serialize)]
struct Request<'q> {
    version: u32,
    tsconfig: String,
    queries: &'q [Query],
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Reply {
    version: u32,
    typescript: String,
    from: String,
    answers: Vec<Option<TscAnswer>>,
}

pub const SCRIPT: &str = include_str!("tsc_sidecar.mjs");

const TYPESCRIPT_UNAVAILABLE: i32 = 3;

pub fn ask(root: &Path, tsconfig: &Path, queries: &[Query]) -> Result<TscReply, TscError> {
    let tsconfig = std::path::absolute(tsconfig).map_err(|error| TscError::Failed {
        status: None,
        stderr: error.to_string(),
    })?;
    let request = serde_json::to_vec(&Request {
        version: PROTOCOL_VERSION,
        tsconfig: tsconfig.to_string_lossy().into_owned(),
        queries,
    })
    .map_err(|error| TscError::Malformed(error.to_string()))?;
    let mut child = Command::new("node")
        .args(["--input-type=module", "--eval", SCRIPT])
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(TscError::NodeUnavailable)?;
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let writer = std::thread::spawn(move || stdin.write_all(&request));
    let output = child
        .wait_with_output()
        .map_err(TscError::NodeUnavailable)?;
    let _ = writer.join();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    match output.status.code() {
        Some(0) => parse_reply(&output.stdout, queries),
        Some(TYPESCRIPT_UNAVAILABLE) => Err(TscError::TypescriptUnavailable(stderr)),
        status => Err(TscError::Failed { status, stderr }),
    }
}

pub fn parse_reply(text: &[u8], queries: &[Query]) -> Result<TscReply, TscError> {
    let reply: Reply =
        serde_json::from_slice(text).map_err(|error| TscError::Malformed(error.to_string()))?;

    if reply.version != PROTOCOL_VERSION {
        return Err(TscError::Malformed(format!(
            "protocol version {} where {PROTOCOL_VERSION} was requested",
            reply.version
        )));
    }

    if reply.answers.len() != queries.len() {
        return Err(TscError::Malformed(format!(
            "{} answers for {} queries",
            reply.answers.len(),
            queries.len()
        )));
    }

    for (index, (query, answer)) in queries.iter().zip(&reply.answers).enumerate() {
        match (query, answer) {
            (_, None)
            | (Query::Type { .. }, Some(TscAnswer::Type(_)))
            | (Query::Callee { .. }, Some(TscAnswer::Callee(_))) => {}
            _ => {
                return Err(TscError::Malformed(format!(
                    "answer {index} does not answer its query kind"
                )))
            }
        }

        if let Some(TscAnswer::Callee(answer)) = answer {
            if let Some(target) = answer
                .targets
                .iter()
                .find(|target| target.start > target.end)
            {
                return Err(TscError::Malformed(format!(
                    "answer {index} targets an inverted span {}..{} in {}",
                    target.start, target.end, target.file
                )));
            }
        }
    }

    Ok(TscReply {
        typescript: reply.typescript,
        from: reply.from,
        answers: reply.answers,
    })
}
