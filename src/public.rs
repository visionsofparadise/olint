use crate::analysis::Analysis;
use crate::config::{Config, ConfigError, Limit};
use crate::declarations::FunctionNode;
use crate::directives::max_tag_of;
use crate::project::FileId;
use crate::unknowns::UnknownId;

#[path = "public_surface.rs"]
mod surface;

pub struct PublicCoverage<'a> {
    pub functions: Vec<PublicFunction<'a>>,
    pub unknowns: Option<UnknownId>,
}

#[derive(Clone)]
pub struct ApplicableLimit {
    pub limit: Limit,
    pub entry: String,
}

pub struct PublicFunction<'a> {
    pub file: FileId,
    pub function: FunctionNode<'a>,
    pub limits: Vec<ApplicableLimit>,
    pub own_limit: bool,
}

pub fn public_roots<'a>(
    analysis: &mut Analysis<'_, 'a>,
    config: &Config,
) -> Result<Vec<(FileId, FunctionNode<'a>)>, ConfigError> {
    Ok(surface::discover(analysis, config)?
        .functions
        .into_iter()
        .map(|function| (function.file, function.function))
        .collect())
}

pub fn public_functions<'a>(
    analysis: &mut Analysis<'_, 'a>,
    config: &Config,
) -> Result<PublicCoverage<'a>, ConfigError> {
    let discovery = surface::discover(analysis, config)?;
    let mut found = discovery.functions;
    let mut unknowns = None;

    for (site, entry, reason) in discovery.issues {
        let origin = analysis.unknowns.origin(site, reason);
        let origin = analysis.unknowns.called(Some(origin), entry);
        unknowns = analysis.unknowns.join(unknowns, origin);
    }

    for public in &mut found {
        if let Some((cost, text)) =
            max_tag_of(&analysis.function_tags(public.file, public.function))
        {
            public.limits = vec![ApplicableLimit {
                limit: Limit { cost, text },
                entry: public.limits[0].entry.clone(),
            }];
            public.own_limit = true;
        }
    }

    for public in &mut found {
        for applicable in &mut public.limits {
            match analysis.bind_function_cost(public.file, public.function, &applicable.limit.cost)
            {
                Ok(cost) => applicable.limit.cost = cost,
                Err(crate::cost::CostError::UnresolvedQuantity(_)) => {}
                Err(error) => {
                    analysis.errors.insert(format!(
                        "invalid limit {} for {}: {error:?}",
                        applicable.limit.text,
                        analysis.name_of(public.file, public.function)
                    ));
                }
            }
        }
    }

    Ok(PublicCoverage {
        functions: found,
        unknowns,
    })
}
