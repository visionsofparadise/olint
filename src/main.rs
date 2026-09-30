use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};

use clap::error::ErrorKind;
use clap::Parser;
use olint::analysis::{Analysis, Options, TypeMode};
use olint::config::{
    read_config, validate_entries, Config, ConfigError, UnknownPolicy, CONFIG_FIELDS,
    ENTRYPOINT_FORMS, LIMIT_FORMS,
};
use olint::cost::CostComparison;
use olint::declarations::FunctionNode;
use olint::project::{FileId, Project, ProjectError};
use olint::public::{public_functions, public_roots};
use olint::regex::{companion_of, RegexError, RegexLimits};
use olint::report::{
    lint_lines, order_by_cost_descending, report_lines, report_rows_of, Finding, Verdict,
};
use olint::tsc::{ask, Query, TscError, TscReply};
use olint::unknowns::{SourceSpan, UnknownReason};
use oxc_allocator::Allocator;
use oxc_span::GetSpan;

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[arg(long, default_value_t = 2)]
    min: u32,
    #[arg(long)]
    report: bool,
    #[arg(long, value_enum, default_value_t = TypeMode::Auto)]
    types: TypeMode,
    #[arg(long)]
    config: Option<PathBuf>,
    #[arg(long, default_value = "./tsconfig.json")]
    tsconfig: PathBuf,
}

enum Failure {
    Project(ProjectError),
    Config(ConfigError),
    Tsc(TscError),
    Regex(RegexError),
    Usage(String),
}

fn single_line_of(text: &str) -> String {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<&str>>()
        .join(" ")
}

impl fmt::Display for Failure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Failure::Config(ConfigError::Root { path, text }) => {
                format!("{} must contain an object, got {text}", path.display())
            }
            Failure::Config(ConfigError::Field { path, field }) => {
                format!(
                    "{}: unsupported field {field:?}; supported fields are {}",
                    path.display(),
                    CONFIG_FIELDS.join(", ")
                )
            }
            Failure::Config(ConfigError::Selection { path, message }) => {
                format!("{}: {message}", path.display())
            }
            Failure::Config(ConfigError::Unknown { value }) => {
                format!("unknown must be ignore, warn or error, got {value}")
            }
            Failure::Project(ProjectError::Tsconfig { path, message }) => {
                format!("{}: {message}", path.display())
            }
            Failure::Project(ProjectError::Read { path, source }) => {
                format!("cannot read {}: {source}", path.display())
            }
            Failure::Project(ProjectError::Parse { path, message }) => {
                format!("cannot parse {}: {message}", path.display())
            }
            Failure::Config(ConfigError::Read { path, source }) => {
                format!("cannot read {}: {source}", path.display())
            }
            Failure::Config(ConfigError::Json { path, message }) => {
                format!("{} is not valid JSON: {message}", path.display())
            }
            Failure::Config(ConfigError::Limit { field, text }) => {
                format!("{field} must be {LIMIT_FORMS}, got {text}")
            }
            Failure::Config(ConfigError::Entrypoints { text }) => {
                format!("entrypoints must be an array of items each {ENTRYPOINT_FORMS}, got {text}")
            }
            Failure::Config(ConfigError::Entrypoint { field, text }) => {
                format!("{field} must be {ENTRYPOINT_FORMS}, got {text}")
            }
            Failure::Config(ConfigError::Ignore { pattern }) => {
                format!("ignore pattern {pattern} is not a valid glob")
            }
            Failure::Tsc(error) => format!("tsc unavailable: {}", reason_of(error)),
            Failure::Regex(RegexError::Malformed(message)) => {
                format!("regex helper replied malformed: {message}")
            }
            Failure::Regex(RegexError::Unavailable(message)) => {
                format!("regex classification unavailable: {message}")
            }
            Failure::Regex(RegexError::Deadline(deadline)) => format!(
                "regex helper exceeded its {} second deadline",
                deadline.as_secs_f64()
            ),
            Failure::Usage(message) => message.clone(),
        };

        write!(formatter, "{}", single_line_of(&message))
    }
}

fn reason_of(error: &TscError) -> String {
    match error {
        TscError::NodeUnavailable(source) => format!("node did not start: {source}"),
        TscError::TypescriptUnavailable(stderr) => single_line_of(stderr),
        TscError::Failed { status, stderr } => match status {
            Some(status) => format!("tsc exited {status}: {}", single_line_of(stderr)),
            None => format!("tsc failed: {}", single_line_of(stderr)),
        },
        TscError::Malformed(message) => format!("tsc replied malformed: {message}"),
    }
}

fn print_lines(lines: &[String]) {
    let mut stdout = std::io::stdout().lock();
    let _ = writeln!(stdout, "{}", lines.join("\n"));
    let _ = stdout.flush();
}

impl From<TscError> for Failure {
    fn from(error: TscError) -> Self {
        Self::Tsc(error)
    }
}

fn roots_of<'a>(
    analysis: &mut Analysis<'_, 'a>,
    config: &Config,
    report: bool,
) -> Result<Vec<(FileId, FunctionNode<'a>)>, Failure> {
    if !report {
        return public_roots(analysis, config).map_err(Failure::Config);
    }

    let mut functions = analysis.reportable();

    if config.explicit_entrypoints {
        let mut selected: std::collections::HashSet<_> = functions
            .iter()
            .map(|(file, function)| (*file, function.node_id()))
            .collect();

        for function in public_roots(analysis, config).map_err(Failure::Config)? {
            if selected.insert((function.0, function.1.node_id())) {
                functions.push(function);
            }
        }
    }

    Ok(functions)
}

fn run(cli: Cli) -> Result<i32, Failure> {
    run_with_ask(cli, ask)
}

fn run_with_ask(
    cli: Cli,
    mut compiler: impl FnMut(&Path, &Path, &[Query]) -> Result<TscReply, TscError>,
) -> Result<i32, Failure> {
    let tsconfig = cli.tsconfig;

    if !tsconfig.is_file() {
        return Err(Failure::Usage(format!(
            "tsconfig {} not found",
            tsconfig.display()
        )));
    }

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).map_err(Failure::Project)?;
    let config = read_config(&project, cli.config.as_deref()).map_err(Failure::Config)?;

    validate_entries(&project, &config).map_err(Failure::Config)?;

    let options = Options {
        minimum_exponent: cli.min,
        types: cli.types,
        record_nodes: false,
    };
    let mut analysis = Analysis::new(&project, options);
    let mut assisted = analysis.options.types != TypeMode::Syntactic;
    let mut rounds = 0;
    let mut sites = 0;
    let helper = std::env::current_exe().map(|executable| companion_of(&executable));

    let functions = loop {
        let functions = if assisted {
            let gathered = analysis.gather_discovered_answers(
                |analysis| roots_of(analysis, &config, cli.report),
                |queries| compiler(&project.root, &project.tsconfig_path, queries),
            );

            match gathered {
                Ok((gathered, functions)) => {
                    rounds += gathered.rounds;
                    sites += gathered.sites;

                    functions
                }
                Err(Failure::Tsc(
                    error @ (TscError::NodeUnavailable(_) | TscError::TypescriptUnavailable(_)),
                )) if analysis.options.types == TypeMode::Auto => {
                    eprintln!(
                        "olint: types from declarations only ({})",
                        reason_of(&error)
                    );
                    analysis.fall_back_to_declarations();

                    assisted = false;

                    roots_of(&mut analysis, &config, cli.report)?
                }
                Err(error) => return Err(error),
            }
        } else {
            roots_of(&mut analysis, &config, cli.report)?
        };
        let classified = analysis.regex_answers.len();
        let unavailable = analysis
            .gather_selected_regex_answers(&functions, |requests| match &helper {
                Ok(helper) => olint::regex::ask(helper, requests, &RegexLimits::default()),
                Err(error) => Err(RegexError::Unavailable(format!(
                    "the olint executable path is unknown ({error})"
                ))),
            })
            .map_err(Failure::Regex)?;

        if let Some(reason) = unavailable {
            eprintln!("olint: regex classification unavailable ({reason})");
        }

        if analysis.regex_answers.len() == classified {
            break functions;
        }
    };

    if assisted {
        eprintln!(
            "tsc: {sites} sites asked in {rounds} rounds, {}",
            analysis.tsc_info
        );
    }

    let public = public_functions(&mut analysis, &config).map_err(Failure::Config)?;

    check_analysis_errors(&analysis)?;

    let mut selected_unknowns: Vec<_> = public.unknowns.into_iter().collect();

    if public.unknowns.is_some() {
        println!("public coverage [partial]");
    }

    let public = public.functions;
    let mut selected_comparisons = Vec::new();
    let code = if cli.report {
        let rows = report_rows_of(&mut analysis, &functions);

        selected_unknowns.extend(rows.iter().filter_map(|row| row.unknowns));

        check_analysis_errors(&analysis)?;
        print_lines(&report_lines(
            &analysis.values,
            &analysis.traces,
            &project,
            &rows,
            analysis.options.minimum_exponent,
        ));

        0
    } else {
        let mut checked = Vec::with_capacity(public.len());

        for public in public {
            let part = analysis
                .summarize(public.file, public.function)
                .total(&mut analysis.unknowns, &mut analysis.traces);

            for applicable in public.limits.iter().filter(|applicable| {
                part.cost.compare(&applicable.limit.cost) == CostComparison::Inconclusive
            }) {
                let span = project
                    .file(public.file)
                    .semantic
                    .nodes()
                    .kind(public.function.node_id())
                    .span();
                let unknown = analysis.unknowns.origin(
                    SourceSpan {
                        file: public.file,
                        start: span.start,
                        end: span.end,
                    },
                    UnknownReason::Comparison,
                );

                // An incomparable limit makes the entry's verdict Inconclusive (§4.3) and leaves its state as it is.
                selected_unknowns.push(unknown);
                selected_comparisons.push(format!(
                    "unknown comparison for {} against {} via {} at {}:{}",
                    analysis.name_of(public.file, public.function),
                    applicable.limit.text,
                    applicable.entry,
                    project.file(public.file).relative,
                    project.line_of(public.file, span.start)
                ));
            }

            checked.push(Finding {
                name: analysis.name_of(public.file, public.function),
                site: analysis.function_site_of(public.file, public.function),
                public,
                part,
            });
        }

        let mut over: Vec<&Finding> = checked
            .iter()
            .filter(|finding| finding.verdict() == Some(Verdict::Exceeds))
            .collect();
        let inconclusive = checked
            .iter()
            .any(|finding| finding.verdict() == Some(Verdict::Inconclusive));

        over.sort_by(|left, right| {
            order_by_cost_descending(&left.part.cost, &right.part.cost)
                .then_with(|| left.name.cmp(&right.name))
        });

        check_analysis_errors(&analysis)?;
        print_lines(&lint_lines(
            &analysis.values,
            &analysis.traces,
            &project,
            &config,
            &checked,
            &over,
        ));

        selected_unknowns.extend(checked.iter().filter_map(|finding| finding.part.unknowns));

        // §4.5 fails on Exceeds and §4.6 on Inconclusive under "error". Every unknown origin still fails under "error"
        // until action 4.6 narrows it to Inconclusive entries (G41).
        i32::from(
            !over.is_empty()
                || (config.unknown == UnknownPolicy::Error
                    && (inconclusive || !selected_unknowns.is_empty())),
        )
    };

    if config.unknown != UnknownPolicy::Ignore {
        let severity = if config.unknown == UnknownPolicy::Error {
            "error"
        } else {
            "warning"
        };
        let mut shown = std::collections::HashSet::new();

        for comparison in selected_comparisons {
            if shown.insert(comparison.clone()) {
                eprintln!("olint: {severity}: {comparison}");
            }
        }

        for root in selected_unknowns {
            for line in analysis.unknowns.lines_with(&project, root, &|id, out| {
                analysis.values.write_label(id, out)
            }) {
                if shown.insert(line.clone()) {
                    eprintln!("olint: {severity}: {line}");
                }
            }
        }
    }

    for warning in &analysis.warnings {
        eprintln!("olint: warning: {warning}");
    }

    eprintln!("{}", analysis.stats.lines().join("\n"));

    Ok(code)
}

fn main() {
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(error) => match error.kind() {
            ErrorKind::DisplayHelp | ErrorKind::DisplayVersion => error.exit(),
            _ => {
                let rendered = error.render().to_string();
                let message = rendered
                    .lines()
                    .find(|line| !line.trim().is_empty())
                    .unwrap_or("invalid arguments")
                    .trim_start_matches("error: ")
                    .to_string();

                eprintln!("olint: {message}");
                std::process::exit(2);
            }
        },
    };

    match run(cli) {
        Ok(code) => std::process::exit(code),
        Err(failure) => {
            eprintln!("olint: {failure}");
            std::process::exit(2);
        }
    }
}

fn check_analysis_errors(analysis: &Analysis<'_, '_>) -> Result<(), Failure> {
    if analysis.errors.is_empty() {
        return Ok(());
    }

    Err(Failure::Usage(
        analysis
            .errors
            .iter()
            .cloned()
            .collect::<Vec<_>>()
            .join("; "),
    ))
}

#[cfg(test)]
#[path = "main.test.rs"]
mod tests;
