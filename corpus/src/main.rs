//! The olint evaluation corpus harness.
//!
//! ```text
//! olint-corpus snapshot --src <sha|tree> [--out <dir>] [--jobs <n>] [--timeout <seconds>] [--member <prefix>]...
//!     [--unknown <policy>]
//! olint-corpus diff <base-sha> <head-sha> [--no-scale]
//! olint-corpus selftest [--member <prefix>]... [--check <n,...>] [--jobs <n>] [--timeout <seconds>] [--work <dir>]
//!     [--refresh true]
//! olint-corpus scale --src <sha|tree> [--family <name>] [--min-k <k>] [--max-k <k>] [--out <file>] [--jobs <n>]
//!     [--timeout <seconds>]
//! ```
//!
//! `diff` accepts a change only with the §5.3 scaling comparison, so `--no-scale` is for iteration, never acceptance.

mod alloc;
mod diff;
#[path = "../families/mod.rs"]
mod families;
mod members;
mod ranking;
mod scale;
mod selftest;
mod snapshot;

#[global_allocator]
static ALLOCATOR: alloc::Counting = alloc::Counting;

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use selftest::{SelftestArgs, CHECKS};
use snapshot::{MemberArgs, Pass, SnapshotArgs};

const USAGE: &str = "usage:
  olint-corpus snapshot --src <sha|tree> [--out <dir>] [--jobs <n>] [--timeout <seconds>] [--member <prefix>]... [--unknown <policy>]
  olint-corpus diff <base-sha> <head-sha> [--no-scale]
  olint-corpus selftest [--member <prefix>]... [--check <n,...>] [--jobs <n>] [--timeout <seconds>] [--work <dir>] [--refresh true]
  olint-corpus scale --src <sha|tree> [--family <name>] [--min-k <k>] [--max-k <k>] [--out <file>] [--jobs <n>] [--timeout <seconds>]";

struct Flags(Vec<(String, String)>);

impl Flags {
    fn parse(arguments: &[String]) -> Result<Flags, String> {
        let mut pairs = Vec::new();
        let mut rest = arguments.iter();

        while let Some(flag) = rest.next() {
            let Some(name) = flag.strip_prefix("--") else {
                return Err(format!("unexpected argument {flag}"));
            };
            let value = rest
                .next()
                .ok_or_else(|| format!("--{name} needs a value"))?;

            pairs.push((name.to_string(), value.clone()));
        }

        Ok(Flags(pairs))
    }

    fn all(&self, name: &str) -> Vec<String> {
        self.0
            .iter()
            .filter(|(flag, _)| flag == name)
            .map(|(_, value)| value.clone())
            .collect()
    }

    fn optional(&self, name: &str) -> Option<String> {
        self.all(name).pop()
    }

    fn required(&self, name: &str) -> Result<String, String> {
        self.optional(name)
            .ok_or_else(|| format!("--{name} is required"))
    }

    fn check(&self, known: &[&str]) -> Result<(), String> {
        match self
            .0
            .iter()
            .find(|(flag, _)| !known.contains(&flag.as_str()))
        {
            Some((flag, _)) => Err(format!("unknown flag --{flag}")),
            None => Ok(()),
        }
    }

    fn number(&self, name: &str, default: u64) -> Result<u64, String> {
        self.optional(name).map_or(Ok(default), |value| {
            value
                .parse()
                .map_err(|_| format!("--{name} must be a whole number, got {value}"))
        })
    }
}

fn default_jobs() -> u64 {
    std::thread::available_parallelism().map_or(1, |count| (count.get() as u64 / 2).clamp(1, 8))
}

fn checks_of(text: Option<String>) -> Result<BTreeSet<u8>, String> {
    let Some(text) = text else {
        return Ok(CHECKS.into_iter().collect());
    };

    text.split(',')
        .map(|check| match check.trim().parse::<u8>() {
            Ok(number) if CHECKS.contains(&number) => Ok(number),
            _ => Err(format!("--check takes numbers from 1 to 5, got {check}")),
        })
        .collect()
}

fn run(arguments: &[String]) -> Result<(), String> {
    let Some((command, rest)) = arguments.split_first() else {
        return Err(USAGE.to_string());
    };

    if command == "diff" {
        return match rest {
            [base, head] => diff::diff(base, head, false),
            [base, head, flag] if flag == "--no-scale" => diff::diff(base, head, true),
            _ => Err(USAGE.to_string()),
        };
    }

    let flags = Flags::parse(rest)?;

    match command.as_str() {
        "snapshot" => {
            flags.check(&["src", "out", "jobs", "timeout", "member", "unknown"])?;

            snapshot::snapshot(SnapshotArgs {
                src: flags.required("src")?,
                out: flags.optional("out").map(PathBuf::from),
                jobs: flags.number("jobs", default_jobs())? as usize,
                timeout: Duration::from_secs(flags.number("timeout", 900)?),
                only: flags.all("member"),
                unknown: flags.optional("unknown"),
            })
        }
        "selftest" => {
            flags.check(&["member", "check", "jobs", "timeout", "work", "refresh"])?;

            selftest::selftest(SelftestArgs {
                only: flags.all("member"),
                checks: checks_of(flags.optional("check"))?,
                jobs: flags.number("jobs", default_jobs())? as usize,
                timeout: Duration::from_secs(flags.number("timeout", 900)?),
                work: flags.optional("work").map(PathBuf::from),
                refresh: match flags.optional("refresh").as_deref() {
                    None | Some("false") => false,
                    Some("true") => true,
                    Some(other) => {
                        return Err(format!("--refresh takes true or false, got {other}"))
                    }
                },
            })
        }
        "scale" => {
            flags.check(&["src", "family", "min-k", "max-k", "out", "jobs", "timeout"])?;

            scale::scale(scale::ScaleArgs {
                src: flags.required("src")?,
                family: flags.optional("family"),
                min_k: match flags.optional("min-k") {
                    Some(_) => Some(flags.number("min-k", 0)? as u32),
                    None => None,
                },
                max_k: flags.number("max-k", u64::from(families::MAX_K))? as u32,
                out: flags.optional("out").map(PathBuf::from),
                jobs: flags.number("jobs", default_jobs())? as usize,
                timeout: Duration::from_secs(flags.number("timeout", 900)?),
            })
        }
        "snapshot-member" => {
            flags.check(&["root", "pass", "rows", "counts", "tree", "unknown"])?;

            let pass = flags.required("pass")?;

            snapshot::snapshot_member(MemberArgs {
                root: PathBuf::from(flags.required("root")?),
                pass: Pass::of(&pass).ok_or_else(|| format!("unknown pass {pass}"))?,
                rows: PathBuf::from(flags.required("rows")?),
                counts: PathBuf::from(flags.required("counts")?),
                tree: PathBuf::from(flags.required("tree")?),
                unknown: flags.optional("unknown"),
            })
        }
        _ => Err(USAGE.to_string()),
    }
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();

    match run(&arguments) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("olint-corpus: {message}");

            ExitCode::FAILURE
        }
    }
}
