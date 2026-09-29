use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant};

use indexmap::IndexSet;
use oxc_ast::ast::{Argument, Expression};
use oxc_ast::AstKind;
use oxc_span::{GetSpan, Span};
use serde::{Deserialize, Serialize};

use crate::analysis::Analysis;
use crate::bounds::short;
use crate::cost::{Cost, CostError, Part};
use crate::declarations::FunctionNode;
use crate::declared_types::Kind;
use crate::native::{native_model_of, Identity, Matching, Pattern, Role};
use crate::project::FileId;
use crate::syntax::unwrap;
use crate::unknowns::UnknownReason;

pub const PROTOCOL_VERSION: u32 = 2;
pub const RECHECK_VERSION: &str = "4.5.0";
pub const QUALIFIED_MODEL: &str = "recheck 4.5.0 automaton ordered backtracking";
pub const HELPER_NAME: &str = "regex_sidecar.mjs";
pub const SCRIPT: &str = include_str!("regex_sidecar.mjs");

const MALFORMED_REQUEST: i32 = 2;
const PACKAGE_UNAVAILABLE: i32 = 3;
const VERSION_MISMATCH: i32 = 4;
const FORBIDDEN_EXECUTION: i32 = 5;
const MAXIMUM_DEGREE: u64 = 16;
const STDERR_BYTES: u64 = 16 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RegexRequest {
    pub source: String,
    pub flags: String,
    pub model: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegexAnswer {
    Bound { cost: Cost, model: String },
    Unknown { reason: String },
    Exhausted { reason: String },
}

#[derive(Debug, PartialEq, Eq)]
pub enum RegexError {
    Unavailable(String),
    Malformed(String),
    Deadline(Duration),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegexLimits {
    pub deadline: Duration,
    pub source_bytes: usize,
    pub requests: usize,
    pub reply_bytes: usize,
    pub heap_megabytes: u32,
}

impl Default for RegexLimits {
    fn default() -> Self {
        RegexLimits {
            deadline: Duration::from_secs(120),
            source_bytes: 4096,
            requests: 1024,
            reply_bytes: 8 * 1024 * 1024,
            heap_megabytes: 512,
        }
    }
}

impl RegexRequest {
    pub fn qualified(source: &str, flags: &str) -> RegexRequest {
        RegexRequest {
            source: source.to_string(),
            flags: flags.to_string(),
            model: QUALIFIED_MODEL.to_string(),
        }
    }

    fn repeats(&self, matching: Matching) -> bool {
        let repeated = match matching {
            Matching::Rejected | Matching::Once => false,
            Matching::Flagged => self.flags.contains('g'),
            Matching::Repeated => true,
        };

        repeated && !is_matched_once(&self.source, &self.flags)
    }
}

pub fn is_matched_once(source: &str, flags: &str) -> bool {
    if flags.contains('m') || !source.starts_with('^') {
        return false;
    }

    let mut depth = 0usize;
    let mut class = 0usize;
    let mut characters = source.chars();

    while let Some(character) = characters.next() {
        match character {
            '\\' => {
                characters.next();
            }
            '[' if class == 0 || flags.contains('v') => class += 1,
            ']' if class > 0 => class -= 1,
            _ if class > 0 => {}
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            '|' if depth == 0 => return false,
            _ => {}
        }
    }

    true
}

pub fn is_context_free(source: &str, flags: &str) -> bool {
    let mut class = 0usize;
    let mut characters = source.chars().peekable();

    while let Some(character) = characters.next() {
        match character {
            '\\' => match characters.next() {
                Some('b' | 'B') if class == 0 => return false,
                _ => {}
            },
            '[' if class == 0 || flags.contains('v') => class += 1,
            ']' if class > 0 => class -= 1,
            _ if class > 0 => {}
            '^' => return false,
            '(' if characters.peek() == Some(&'?') => {
                let lookbehind: String = characters.clone().take(3).collect();

                if lookbehind == "?<=" || lookbehind == "?<!" {
                    return false;
                }
            }
            _ => {}
        }
    }

    true
}

impl RegexAnswer {
    pub fn cost_of(&self, subject: &Cost) -> Option<Result<Cost, CostError>> {
        match self {
            RegexAnswer::Bound { cost, .. } => Some(
                (0..=MAXIMUM_DEGREE)
                    .find(|degree| degree_cost_of(*degree).as_ref() == Ok(cost))
                    .ok_or(CostError::Domain)
                    .and_then(|degree| match degree {
                        0 => Ok(Cost::ONE),
                        _ => Cost::power(subject.clone(), Cost::constant(degree)),
                    }),
            ),
            RegexAnswer::Unknown { .. } | RegexAnswer::Exhausted { .. } => None,
        }
    }
}

fn degree_cost_of(degree: u64) -> Result<Cost, CostError> {
    match degree {
        0 => Ok(Cost::ONE),
        _ => Cost::power(Cost::N, Cost::constant(degree)),
    }
}

#[derive(Serialize)]
struct WireRequest<'r> {
    version: u32,
    requests: Vec<WireEntry<'r>>,
}

#[derive(Serialize)]
struct WireEntry<'r> {
    source: &'r str,
    flags: &'r str,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    version: u32,
    recheck: String,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Status {
    Safe,
    Vulnerable,
    Unknown,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Checker {
    Automaton,
    Fuzz,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Class {
    Constant,
    Linear,
    Safe,
    Polynomial,
    Exponential,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum Failure {
    Unsupported,
    Invalid,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct Complexity {
    #[serde(rename = "type")]
    class: Class,
    degree: Option<serde_json::Number>,
    is_fuzz: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Reply {
    source: String,
    flags: String,
    status: Status,
    checker: Option<Checker>,
    complexity: Option<Complexity>,
    error: Option<Failure>,
}

enum Line {
    Text(String),
    Oversized,
    Undecodable,
}

enum Stop {
    Closed,
    Deadline,
}

pub fn companion_of(executable: &Path) -> PathBuf {
    executable.with_file_name(HELPER_NAME)
}

pub fn ask(
    helper: &Path,
    requests: &[RegexRequest],
    limits: &RegexLimits,
) -> Result<Vec<RegexAnswer>, RegexError> {
    let mut answers: Vec<Option<RegexAnswer>> = vec![None; requests.len()];
    let mut sent = Vec::new();

    for (index, request) in requests.iter().enumerate() {
        answers[index] = if request.model != QUALIFIED_MODEL {
            Some(RegexAnswer::Unknown {
                reason: format!("matching model {:?} is not qualified", request.model),
            })
        } else if request.source.len() + request.flags.len() > limits.source_bytes {
            Some(RegexAnswer::Exhausted {
                reason: format!("pattern exceeds {} bytes", limits.source_bytes),
            })
        } else if sent.len() >= limits.requests {
            Some(RegexAnswer::Exhausted {
                reason: format!("more than {} patterns", limits.requests),
            })
        } else {
            sent.push(index);

            None
        };
    }

    if !sent.is_empty() {
        let replies = exchange(helper, requests, &sent, limits)?;

        for (index, answer) in sent.into_iter().zip(replies) {
            answers[index] = Some(answer);
        }
    }

    Ok(answers
        .into_iter()
        .map(|answer| answer.expect("every request is answered"))
        .collect())
}

fn exchange(
    helper: &Path,
    requests: &[RegexRequest],
    sent: &[usize],
    limits: &RegexLimits,
) -> Result<Vec<RegexAnswer>, RegexError> {
    let helper = std::path::absolute(helper).unwrap_or_else(|_| helper.to_path_buf());
    let script = std::fs::read(&helper).map_err(|error| {
        RegexError::Unavailable(format!(
            "companion helper {} cannot be read ({error}); install {HELPER_NAME} beside the olint executable",
            helper.display()
        ))
    })?;

    if script != SCRIPT.as_bytes() {
        return Err(RegexError::Unavailable(format!(
            "companion helper {} does not match this olint build; reinstall olint",
            helper.display()
        )));
    }

    let wire = serde_json::to_vec(&WireRequest {
        version: PROTOCOL_VERSION,
        requests: sent
            .iter()
            .map(|index| WireEntry {
                source: &requests[*index].source,
                flags: &requests[*index].flags,
            })
            .collect(),
    })
    .map_err(|error| RegexError::Malformed(error.to_string()))?;
    let mut command = Command::new("node");

    command
        .arg(format!("--max-old-space-size={}", limits.heap_megabytes))
        .arg(&helper)
        .env_remove("NODE_PATH")
        .env_remove("NODE_OPTIONS")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(directory) = helper.parent() {
        command.current_dir(directory);
    }

    let mut child = command.spawn().map_err(|error| {
        RegexError::Unavailable(format!(
            "node did not start ({error}); install Node.js 24 or later on PATH"
        ))
    })?;
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let stdout = child.stdout.take().expect("stdout is piped");
    let mut stderr = child.stderr.take().expect("stderr is piped");
    let writer = std::thread::spawn(move || {
        let _ = stdin.write_all(&wire);
    });
    let errors = std::thread::spawn(move || {
        let mut text = String::new();
        let _ = (&mut stderr).take(STDERR_BYTES).read_to_string(&mut text);
        let _ = std::io::copy(&mut stderr, &mut std::io::sink());

        text
    });
    let line_bytes = limits.source_bytes * 6 + 1024;
    let reply_bytes = limits.reply_bytes;
    let (sender, receiver) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut consumed = 0;

        loop {
            let mut buffer = Vec::new();
            let limit = u64::try_from(line_bytes + 1).unwrap_or(u64::MAX);

            match (&mut reader).take(limit).read_until(b'\n', &mut buffer) {
                Ok(0) | Err(_) => break,
                Ok(read) => consumed += read,
            }

            if buffer.len() > line_bytes || consumed > reply_bytes {
                let _ = sender.send(Line::Oversized);

                break;
            }

            if buffer.ends_with(b"\n") {
                buffer.pop();
            }

            let line = match String::from_utf8(buffer) {
                Ok(text) => Line::Text(text),
                Err(_) => Line::Undecodable,
            };

            if sender.send(line).is_err() {
                break;
            }
        }
    });
    let deadline = Instant::now() + limits.deadline;
    let mut header = false;
    let mut replies = Vec::with_capacity(sent.len());
    let outcome = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());

        match receiver.recv_timeout(remaining) {
            Ok(Line::Text(text)) if !header => match check_header(&text) {
                Ok(()) => header = true,
                Err(error) => break Err(error),
            },
            Ok(Line::Text(text)) => {
                let Some(index) = sent.get(replies.len()) else {
                    break Err(RegexError::Malformed(format!(
                        "more than {} answers",
                        sent.len()
                    )));
                };

                match answer_of(&text, &requests[*index]) {
                    Ok(answer) => replies.push(answer),
                    Err(error) => break Err(error),
                }
            }
            Ok(Line::Oversized) => {
                break Err(RegexError::Malformed(format!(
                    "reply exceeds {line_bytes} bytes per line or {reply_bytes} bytes in total"
                )))
            }
            Ok(Line::Undecodable) => {
                break Err(RegexError::Malformed("reply is not UTF-8".to_string()))
            }
            Err(RecvTimeoutError::Timeout) => break Ok(Stop::Deadline),
            Err(RecvTimeoutError::Disconnected) => break Ok(Stop::Closed),
        }
    };

    if !matches!(outcome, Ok(Stop::Closed)) {
        let _ = child.kill();
    }

    let status = status_of(&mut child, deadline);

    drop(receiver);

    let _ = writer.join();
    let _ = reader.join();

    let stderr = errors
        .join()
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<&str>>()
        .join(" ");
    let exhausted = |reason: String, mut replies: Vec<RegexAnswer>| {
        replies.resize(
            sent.len(),
            RegexAnswer::Exhausted {
                reason: reason.clone(),
            },
        );

        Ok(replies)
    };

    match outcome? {
        Stop::Deadline => Err(RegexError::Deadline(limits.deadline)),
        Stop::Closed => match status {
            Some(0) if replies.len() == sent.len() => Ok(replies),
            Some(0) => Err(RegexError::Malformed(format!(
                "{} answers for {} requests",
                replies.len(),
                sent.len()
            ))),
            Some(PACKAGE_UNAVAILABLE | VERSION_MISMATCH) => Err(RegexError::Unavailable(format!(
                "{stderr}; reinstall olint with its pinned recheck {RECHECK_VERSION}"
            ))),
            Some(FORBIDDEN_EXECUTION) => Err(RegexError::Malformed(stderr)),
            Some(MALFORMED_REQUEST) => Err(RegexError::Malformed(stderr)),
            status => exhausted(
                format!(
                    "regex helper stopped with status {}: {stderr}",
                    status.map_or("none".to_string(), |code| code.to_string())
                ),
                replies,
            ),
        },
    }
}

fn status_of(child: &mut Child, deadline: Instant) -> Option<i32> {
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return status.code(),
            Ok(None) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(10)),
            Ok(None) => {
                let _ = child.kill();

                return child.wait().ok().and_then(|status| status.code());
            }
            Err(_) => return None,
        }
    }
}

fn check_header(text: &str) -> Result<(), RegexError> {
    let header: Header = serde_json::from_str(text)
        .map_err(|error| RegexError::Malformed(format!("header: {error}")))?;

    if header.version != PROTOCOL_VERSION {
        return Err(RegexError::Malformed(format!(
            "protocol version {} where {PROTOCOL_VERSION} was requested",
            header.version
        )));
    }

    if header.recheck != RECHECK_VERSION {
        return Err(RegexError::Unavailable(format!(
            "recheck {} answered where {RECHECK_VERSION} is required; reinstall olint",
            header.recheck
        )));
    }

    Ok(())
}

fn answer_of(text: &str, request: &RegexRequest) -> Result<RegexAnswer, RegexError> {
    let reply: Reply =
        serde_json::from_str(text).map_err(|error| RegexError::Malformed(error.to_string()))?;

    if reply.source != request.source || reply.flags != request.flags {
        return Err(RegexError::Malformed(format!(
            "answer for /{}/{} where /{}/{} was requested",
            reply.source, reply.flags, request.source, request.flags
        )));
    }

    if reply.checker == Some(Checker::Fuzz)
        || reply
            .complexity
            .as_ref()
            .is_some_and(|complexity| complexity.is_fuzz)
    {
        return Err(RegexError::Malformed(format!(
            "fuzz answer for /{}/{}",
            reply.source, reply.flags
        )));
    }

    match (reply.status, reply.complexity, reply.error) {
        (Status::Unknown, None, Some(Failure::Unsupported)) => Ok(RegexAnswer::Unknown {
            reason: "recheck does not support this pattern".to_string(),
        }),
        (Status::Unknown, None, Some(Failure::Invalid)) => Ok(RegexAnswer::Unknown {
            reason: "recheck rejects this pattern or its flags".to_string(),
        }),
        (Status::Safe | Status::Vulnerable, Some(complexity), None)
            if reply.checker == Some(Checker::Automaton) =>
        {
            classified_of(complexity)
        }
        _ => Err(RegexError::Malformed(format!(
            "inconsistent answer for /{}/{}",
            reply.source, reply.flags
        ))),
    }
}

fn classified_of(complexity: Complexity) -> Result<RegexAnswer, RegexError> {
    let bound = |cost: Cost| RegexAnswer::Bound {
        cost,
        model: QUALIFIED_MODEL.to_string(),
    };

    match (complexity.class, complexity.degree) {
        (Class::Polynomial, Some(degree)) => match degree.as_u64() {
            Some(degree @ 1..=MAXIMUM_DEGREE) => degree_cost_of(degree)
                .map(bound)
                .map_err(|error| RegexError::Malformed(format!("{error:?}"))),
            _ => Ok(RegexAnswer::Unknown {
                reason: format!("polynomial degree {degree} is not a positive bounded integer"),
            }),
        },
        (Class::Polynomial, None) => Ok(RegexAnswer::Unknown {
            reason: "polynomial answer has no degree".to_string(),
        }),
        (_, Some(_)) => Err(RegexError::Malformed(
            "degree on a non-polynomial answer".to_string(),
        )),
        (Class::Constant, None) => degree_cost_of(0)
            .map(bound)
            .map_err(|error| RegexError::Malformed(format!("{error:?}"))),
        (Class::Linear, None) => degree_cost_of(1)
            .map(bound)
            .map_err(|error| RegexError::Malformed(format!("{error:?}"))),
        (Class::Safe, None) => Ok(RegexAnswer::Unknown {
            reason: "recheck reports safe without a complexity class".to_string(),
        }),
        (Class::Exponential, None) => Ok(RegexAnswer::Unknown {
            reason: "exponential backtracking has no qualified bound".to_string(),
        }),
    }
}

enum PatternSource {
    Classified(RegexRequest),
    Primitive,
    Dynamic,
}

fn compiled_flags_of(pattern: Pattern) -> &'static str {
    match pattern.matching {
        Matching::Repeated => "g",
        _ => "",
    }
}

fn request_of_kind(kind: &AstKind<'_>) -> Option<RegexRequest> {
    match kind {
        AstKind::RegExpLiteral(literal) => Some(RegexRequest::qualified(
            literal.regex.pattern.text.as_str(),
            &literal.regex.flags.to_string(),
        )),
        AstKind::CallExpression(call) => {
            let member = call.callee.as_member_expression()?;
            let name = member.static_property_name()?;
            let model = native_model_of(Identity::Receiver(Kind::String), name)?;
            let Some(Role::Pattern(pattern)) = model.arguments.first() else {
                return None;
            };
            let Some(Argument::StringLiteral(literal)) = call.arguments.first() else {
                return None;
            };

            match pattern.compiles {
                true => Some(RegexRequest::qualified(
                    literal.value.as_str(),
                    compiled_flags_of(*pattern),
                )),
                false => None,
            }
        }
        _ => None,
    }
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn regex_requests_of(&self) -> Vec<RegexRequest> {
        let mut requests = IndexSet::new();

        for file in &self.project.files {
            for node in file.semantic.nodes().iter() {
                if let Some(request) = request_of_kind(&node.kind()) {
                    requests.insert(request);
                }
            }
        }

        requests.into_iter().collect()
    }

    pub fn gather_regex_answers(
        &mut self,
        ask: impl FnOnce(&[RegexRequest]) -> Result<Vec<RegexAnswer>, RegexError>,
    ) -> Result<Option<String>, RegexError> {
        self.gather_regex_requests(self.regex_requests_of(), ask)
    }

    pub fn gather_selected_regex_answers(
        &mut self,
        functions: &[(FileId, FunctionNode<'a>)],
        mut ask: impl FnMut(&[RegexRequest]) -> Result<Vec<RegexAnswer>, RegexError>,
    ) -> Result<Option<String>, RegexError> {
        let mut unavailable = None;

        loop {
            self.reset_between_passes();
            self.needed_regex.clear();
            self.summarize_reportable(functions);

            let requests: Vec<_> = self
                .needed_regex
                .iter()
                .filter(|request| !self.regex_answers.contains_key(*request))
                .cloned()
                .collect();

            if requests.is_empty() {
                self.reset_between_passes();

                return Ok(unavailable);
            }

            if let Some(reason) = self.gather_regex_requests(requests, &mut ask)? {
                unavailable = Some(reason);
            }
        }
    }

    fn gather_regex_requests(
        &mut self,
        requests: Vec<RegexRequest>,
        ask: impl FnOnce(&[RegexRequest]) -> Result<Vec<RegexAnswer>, RegexError>,
    ) -> Result<Option<String>, RegexError> {
        if requests.is_empty() {
            return Ok(None);
        }

        let (answers, unavailable) = match ask(&requests) {
            Ok(answers) if answers.len() == requests.len() => (answers, None),
            Ok(answers) => {
                return Err(RegexError::Malformed(format!(
                    "{} answers for {} requests",
                    answers.len(),
                    requests.len()
                )))
            }
            Err(RegexError::Unavailable(reason)) => (
                vec![
                    RegexAnswer::Unknown {
                        reason: reason.clone()
                    };
                    requests.len()
                ],
                Some(reason),
            ),
            Err(error) => return Err(error),
        };

        self.regex_answers.extend(requests.into_iter().zip(answers));

        Ok(unavailable)
    }

    pub fn regex_answer_of(&self, request: &RegexRequest) -> RegexAnswer {
        self.regex_answers
            .get(request)
            .cloned()
            .unwrap_or_else(|| RegexAnswer::Unknown {
                reason: "regex classification was not requested".to_string(),
            })
    }

    fn pattern_source_of(
        &mut self,
        file: FileId,
        expression: &'a Expression<'a>,
        pattern: Pattern,
    ) -> PatternSource {
        match unwrap(expression) {
            Expression::RegExpLiteral(literal) => {
                PatternSource::Classified(RegexRequest::qualified(
                    literal.regex.pattern.text.as_str(),
                    &literal.regex.flags.to_string(),
                ))
            }
            Expression::StringLiteral(literal) if pattern.compiles => PatternSource::Classified(
                RegexRequest::qualified(literal.value.as_str(), compiled_flags_of(pattern)),
            ),
            _ if !pattern.compiles && self.is_primitive_operand(file, expression) => {
                PatternSource::Primitive
            }
            _ => PatternSource::Dynamic,
        }
    }

    pub(crate) fn is_matched_once_pattern(&self, expression: &'a Expression<'a>) -> bool {
        match unwrap(expression) {
            Expression::RegExpLiteral(literal) => is_matched_once(
                literal.regex.pattern.text.as_str(),
                &literal.regex.flags.to_string(),
            ),
            _ => false,
        }
    }

    pub(crate) fn matching_part_of(
        &mut self,
        (file, span): (FileId, Span),
        expression: &'a Expression<'a>,
        pattern: Pattern,
        subject: &Cost,
    ) -> Part {
        if pattern.matching == Matching::Rejected {
            return Part::none();
        }

        let request = match self.pattern_source_of(file, expression, pattern) {
            PatternSource::Primitive => return Part::none(),
            PatternSource::Dynamic => {
                return self.unknown_part(file, expression.span(), UnknownReason::UnsupportedModel)
            }
            PatternSource::Classified(request) => request,
        };

        if subject.is_one() {
            return Part::none();
        }

        self.needed_regex.insert(request.clone());

        let answer = self.regex_answer_of(&request);
        let repeats = request.repeats(pattern.matching);
        let counted = repeats && is_context_free(&request.source, &request.flags);
        let searched = match answer.cost_of(subject) {
            Some(Ok(cost)) if counted => Some(subject.multiply(&cost)),
            searched => searched,
        };
        let classified = match searched {
            Some(Ok(cost)) if cost.is_one() => Part::none(),
            Some(Ok(cost)) => {
                let suffix = match counted {
                    true => " [regexp, every match]",
                    false => " [regexp]",
                };
                let label = format!("{}{suffix}", short(self.text_of(file, expression.span())));
                let site = self.project.site_of(file, span);
                let origin = self.source_span(file, span);

                crate::cost::nest(
                    label,
                    site,
                    origin,
                    cost,
                    Part::unmarked(Cost::ONE, None),
                    &mut self.unknowns,
                    &mut self.traces,
                )
            }
            Some(Err(_)) => {
                self.unknown_part(file, expression.span(), UnknownReason::ResourceExhaustion)
            }
            None => {
                let reason = match answer {
                    RegexAnswer::Exhausted { .. } => UnknownReason::ResourceExhaustion,
                    _ => UnknownReason::UnsupportedModel,
                };

                self.unknown_part(file, expression.span(), reason)
            }
        };

        match repeats && !counted && matches!(answer, RegexAnswer::Bound { .. }) {
            true => {
                let repeated = self.unknown_part(file, span, UnknownReason::UnsupportedModel);

                classified.max(repeated, &mut self.unknowns, &mut self.traces)
            }
            false => classified,
        }
    }
}
