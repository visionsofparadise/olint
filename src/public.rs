use std::collections::HashMap;

use oxc_ast::ast::{BindingPattern, ClassElement, PropertyKey, TSAccessibility};
use oxc_semantic::NodeId;

use crate::analysis::Analysis;
use crate::annotations::{max_tag_of, PerfTag};
use crate::config::{Config, Limit};
use crate::declarations::{function_of_initializer, Declaration, FunctionNode};
use crate::paths::relative_path_of;
use crate::project::FileId;

pub struct PublicFunction<'a> {
    pub file: FileId,
    pub function: FunctionNode<'a>,
    pub limit: Limit,
    pub own_limit: bool,
    pub entry: String,
}

fn is_hidden(accessibility: Option<TSAccessibility>, key: &PropertyKey<'_>) -> bool {
    matches!(
        accessibility,
        Some(TSAccessibility::Private | TSAccessibility::Protected)
    ) || matches!(key, PropertyKey::PrivateIdentifier(_))
}

fn declared_functions_of(declaration: Declaration<'_>) -> Vec<(FileId, FunctionNode<'_>)> {
    match declaration {
        Declaration::Function { file, function } => match function {
            FunctionNode::Function(inner) if inner.body.is_none() => Vec::new(),
            _ => vec![(file, function)],
        },
        Declaration::Variable {
            file, declarator, ..
        } if matches!(declarator.id, BindingPattern::BindingIdentifier(_)) => {
            function_of_initializer(declarator.init.as_ref())
                .map(|function| vec![(file, function)])
                .unwrap_or_default()
        }
        Declaration::Class { file, class } if class.is_declaration() => class
            .body
            .body
            .iter()
            .filter_map(|element| match element {
                ClassElement::MethodDefinition(method)
                    if !is_hidden(method.accessibility, &method.key)
                        && method.value.body.is_some() =>
                {
                    Some((file, FunctionNode::Function(&method.value)))
                }
                ClassElement::PropertyDefinition(property)
                    if !is_hidden(property.accessibility, &property.key) =>
                {
                    function_of_initializer(property.value.as_ref())
                        .map(|function| (file, function))
                }
                ClassElement::AccessorProperty(property)
                    if !is_hidden(property.accessibility, &property.key) =>
                {
                    function_of_initializer(property.value.as_ref())
                        .map(|function| (file, function))
                }
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

pub fn public_functions<'a>(
    analysis: &mut Analysis<'_, 'a>,
    config: &Config,
) -> Vec<PublicFunction<'a>> {
    let project = analysis.project;
    let mut found: Vec<PublicFunction<'a>> = Vec::new();
    let mut positions: HashMap<(FileId, NodeId), usize> = HashMap::new();

    for (entry_path, limit) in &config.entrypoints {
        let entry = relative_path_of(&project.root, entry_path);
        let Some(entry_file) = project.file_by_path(entry_path) else {
            eprintln!("olint: entrypoint {entry} is not in the project");

            continue;
        };

        for (_, declarations) in analysis.declarations.exports_of(project, entry_file) {
            for declaration in declarations {
                for (file, function) in declared_functions_of(declaration) {
                    let source = project.file(file);

                    if !project.is_project_file(file)
                        || project.is_test_path(file)
                        || config.is_ignored(&source.relative)
                        || analysis
                            .function_tags(file, function)
                            .contains(&PerfTag::Ignore)
                    {
                        continue;
                    }

                    match positions.get(&(file, function.node_id())) {
                        Some(position) => {
                            let known = &mut found[*position];

                            if known.limit.cost.exceeds(limit.cost) {
                                known.limit = limit.clone();
                                known.entry = entry.clone();
                            }
                        }
                        None => {
                            positions.insert((file, function.node_id()), found.len());
                            found.push(PublicFunction {
                                file,
                                function,
                                limit: limit.clone(),
                                own_limit: false,
                                entry: entry.clone(),
                            });
                        }
                    }
                }
            }
        }
    }

    for public in &mut found {
        if let Some((cost, text)) =
            max_tag_of(&analysis.function_tags(public.file, public.function))
        {
            public.limit = Limit { cost, text };
            public.own_limit = true;
        }
    }

    found
}
