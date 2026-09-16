use std::fmt;
use std::io::Write;
use std::path::PathBuf;

use clap::error::ErrorKind;
use clap::Parser;
use olint::analysis::{Analysis, Options, TypeMode};
use olint::config::{read_config, ConfigError, ENTRYPOINT_FORMS, LIMIT_FORMS};
use olint::project::{Project, ProjectError};
use olint::public::public_functions;
use olint::report::{lint_lines, order_by_cost_descending, report_lines, report_rows_of, Finding};
use olint::tsc::{ask, TscError};
use oxc_allocator::Allocator;

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

fn run(cli: Cli) -> Result<i32, Failure> {
    let tsconfig = cli.tsconfig;

    if !tsconfig.is_file() {
        return Err(Failure::Usage(format!(
            "tsconfig {} not found",
            tsconfig.display()
        )));
    }

    let allocator = Allocator::default();
    let project = Project::load(&allocator, &tsconfig).map_err(Failure::Project)?;
    let options = Options {
        minimum_exponent: cli.min,
        types: cli.types,
    };
    let mut analysis = Analysis::new(&project, options);
    let functions = analysis.reportable();

    if analysis.options.types != TypeMode::Syntactic {
        let gathered = analysis.gather_answers(&functions, |queries| {
            ask(&project.root, &project.tsconfig_path, queries)
        });

        match gathered {
            Ok(rounds) => eprintln!(
                "tsc: {} sites asked in {} rounds, {}",
                rounds.sites, rounds.rounds, analysis.tsc_info
            ),
            Err(error @ (TscError::NodeUnavailable(_) | TscError::TypescriptUnavailable(_)))
                if analysis.options.types == TypeMode::Auto =>
            {
                eprintln!(
                    "olint: types from declarations only ({})",
                    reason_of(&error)
                );

                analysis.fall_back_to_declarations();
            }
            Err(error) => return Err(Failure::Tsc(error)),
        }
    }

    let config = read_config(&project, cli.config.as_deref()).map_err(Failure::Config)?;
    let public = public_functions(&mut analysis, &config);
    let code = if cli.report {
        let rows = report_rows_of(&mut analysis, &functions);

        print_lines(&report_lines(
            &project,
            &rows,
            analysis.options.minimum_exponent,
        ));

        0
    } else {
        let mut checked = Vec::with_capacity(public.len());

        for public in public {
            let part = analysis.summarize(public.file, public.function).total();

            checked.push(Finding {
                name: analysis.name_of(public.file, public.function),
                site: analysis.function_site_of(public.file, public.function),
                public,
                part,
            });
        }

        let mut over: Vec<&Finding> = checked
            .iter()
            .filter(|finding| finding.part.cost.exceeds(finding.public.limit.cost))
            .collect();

        over.sort_by(|left, right| order_by_cost_descending(left.part.cost, right.part.cost));

        print_lines(&lint_lines(&project, &config, &checked, &over));

        i32::from(!over.is_empty())
    };

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
