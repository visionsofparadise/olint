use oxc_allocator::UnstableAddress;
use oxc_ast::ast::*;
use oxc_ecmascript::ConstantValue;
use oxc_semantic::{NodeId, Semantic, SymbolId};

use crate::values::{CertifiedValues, Failure, Primitive, PrimitiveAdapter, ValueResult};

#[derive(Debug)]
pub struct EnumInitializer {
    pub symbol: SymbolId,
    pub member: NodeId,
    pub initializer: Option<NodeId>,
    pub value: Result<Primitive, Failure>,
}

pub fn evaluate_enum<'a>(
    semantic: &Semantic<'a>,
    declaration: &TSEnumDeclaration<'a>,
    adapter: &mut PrimitiveAdapter<'_, 'a>,
) -> Result<Vec<EnumInitializer>, Failure> {
    if !adapter.owns_semantic(semantic)
        || !adapter.owns_node(declaration.node_id(), declaration.unstable_address())
    {
        return Err(Failure::UncertifiedReference);
    }

    if declaration.declare {
        return Err(Failure::Unsupported);
    }

    let owner = declaration
        .id
        .symbol_id
        .get()
        .ok_or(Failure::UncertifiedReference)?;
    let scope = declaration
        .body
        .scope_id
        .get()
        .ok_or(Failure::UncertifiedReference)?;
    let mut certified = CertifiedValues::new(semantic);
    let mut results = Vec::new();
    let mut previous = Some(ConstantValue::Number(-1.0));

    for member in &declaration.body.members {
        adapter.visit_container()?;

        let name = match &member.id {
            TSEnumMemberName::Identifier(name) => name.name.as_str(),
            TSEnumMemberName::String(name) | TSEnumMemberName::ComputedString(name)
                if !name.lone_surrogates =>
            {
                name.value.as_str()
            }
            _ => return Err(Failure::Unsupported),
        };

        adapter.reserve_name(name.len())?;

        let symbol = semantic
            .scoping()
            .get_binding(scope, name.into())
            .ok_or(Failure::UncertifiedReference)?;
        let value = if let Some(initializer) = &member.initializer {
            let ValueResult { value, .. } = adapter.evaluate(initializer, &certified);

            value.and_then(|value| {
                if matches!(value, ConstantValue::Number(_) | ConstantValue::String(_)) {
                    Ok(value)
                } else {
                    Err(Failure::Unsupported)
                }
            })
        } else if let Some(ConstantValue::Number(value)) = &previous {
            Ok(ConstantValue::Number(value + 1.0))
        } else {
            Err(Failure::UncertifiedReference)
        };
        let closed = match &member.initializer {
            Some(expression) => adapter.closed_initializer(expression)?,
            None => true,
        };

        if !closed || value.is_err() {
            certified.symbols.clear();
            certified.members.clear();
        }

        previous = match &value {
            Ok(value) => Some(adapter.copy_value(value)?),
            Err(_) => None,
        };

        if closed {
            if let Ok(value) = &value {
                certified.symbols.insert(symbol, adapter.copy_value(value)?);
                certified.members.insert((owner, name.to_owned()), symbol);
            }
        }

        results.push(EnumInitializer {
            symbol,
            member: member.node_id(),
            initializer: member.initializer.as_ref().map(Expression::node_id),
            value,
        });
    }

    Ok(results)
}

#[cfg(test)]
#[path = "enum_values.test.rs"]
mod tests;
