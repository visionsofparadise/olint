//! The olint evaluation corpus harness.
//!
//! ```text
//! olint-corpus snapshot --src <sha|tree> [--out <dir>] [--jobs <n>] [--timeout <seconds>] [--member <prefix>]...
//! ```

mod members;
mod snapshot;

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use snapshot::{MemberArgs, Pass, SnapshotArgs};

const USAGE: &str = "usage: olint-corpus snapshot --src <sha|tree> [--out <dir>] [--jobs <n>] [--timeout <seconds>] [--member <prefix>]...";

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

fn run(arguments: &[String]) -> Result<(), String> {
    let Some((command, rest)) = arguments.split_first() else {
        return Err(USAGE.to_string());
    };
    let flags = Flags::parse(rest)?;

    match command.as_str() {
        "snapshot" => {
            flags.check(&["src", "out", "jobs", "timeout", "member"])?;

            snapshot::snapshot(SnapshotArgs {
                src: flags.required("src")?,
                out: flags.optional("out").map(PathBuf::from),
                jobs: flags.number("jobs", default_jobs())? as usize,
                timeout: Duration::from_secs(flags.number("timeout", 900)?),
                only: flags.all("member"),
            })
        }
        "snapshot-member" => {
            flags.check(&["root", "pass", "rows", "counts", "tree"])?;

            let pass = flags.required("pass")?;

            snapshot::snapshot_member(MemberArgs {
                root: PathBuf::from(flags.required("root")?),
                pass: Pass::of(&pass).ok_or_else(|| format!("unknown pass {pass}"))?,
                rows: PathBuf::from(flags.required("rows")?),
                counts: PathBuf::from(flags.required("counts")?),
                tree: PathBuf::from(flags.required("tree")?),
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
