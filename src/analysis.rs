use std::collections::HashMap;

use indexmap::IndexMap;
use oxc_semantic::NodeId;

use crate::annotations::PerfTag;
use crate::declarations::Declarations;
use crate::oracle::{OracleAnswer, Query};
use crate::project::{FileId, Project};
use crate::types::{OraclePass, QueryKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum TypeMode {
    Auto,
    Oracle,
    Syntactic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    pub strings_linear: bool,
    pub callbacks: bool,
    pub minimum_exponent: u32,
    pub types: TypeMode,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats(IndexMap<String, u32>);

impl Stats {
    pub fn count(&mut self, label: &str) {
        *self.0.entry(label.to_string()).or_insert(0) += 1;
    }

    pub fn lines(&self) -> Vec<String> {
        let mut entries: Vec<(&String, &u32)> = self.0.iter().collect();

        entries.sort_by_key(|(_, count)| std::cmp::Reverse(**count));

        entries
            .into_iter()
            .map(|(label, count)| format!("{count:>5}  {label}"))
            .collect()
    }
}

pub struct Analysis<'p, 'a> {
    pub project: &'p Project<'a>,
    pub declarations: Declarations<'a>,
    pub options: Options,
    pub stats: Stats,
    pub(crate) tag_cache: HashMap<(FileId, NodeId), Vec<PerfTag>>,
    pub pass: OraclePass,
    pub needed: IndexMap<(FileId, u32, u32, QueryKind), Query>,
    pub answers: HashMap<(FileId, u32, u32, QueryKind), Option<OracleAnswer>>,
    pub oracle_info: String,
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub fn new(project: &'p Project<'a>, options: Options) -> Self {
        Analysis {
            project,
            declarations: Declarations::new(project),
            options,
            stats: Stats::default(),
            tag_cache: HashMap::new(),
            pass: OraclePass::Off,
            needed: IndexMap::new(),
            answers: HashMap::new(),
            oracle_info: String::new(),
        }
    }
}
