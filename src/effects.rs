use crate::analysis::work::Event;
use crate::analysis::Analysis;
use crate::declarations::Binding;
use crate::declarations::Declaration;
use crate::project::FileId;
use crate::syntax::{identifier_of, Root};
use crate::values::ValueId;
use oxc_ast::AstKind;

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Effects {
    pub binding_writes: Vec<Binding>,
    pub member_writes: Vec<ValueId>,
    pub escapes: Vec<ValueId>,
    pub unknown_reachable: Vec<ValueId>,
    pub unknown_global: bool,
}

impl<'p, 'a> Analysis<'p, 'a> {
    pub(crate) fn record_write_effects(&mut self, file: FileId, kind: AstKind<'a>) {
        let reference = match kind {
            AstKind::AssignmentExpression(assignment) => match &assignment.left {
                oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(reference) => {
                    Some(reference)
                }
                _ => None,
            },
            AstKind::UpdateExpression(update) => match &update.argument {
                oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(reference) => {
                    Some(reference)
                }
                _ => None,
            },
            _ => return,
        };

        if let Some(binding) =
            reference.and_then(|reference| self.binding_of_identifier(file, reference))
        {
            if !self.current_effects.binding_writes.contains(&binding) {
                self.current_effects.binding_writes.push(binding);
            }
        } else {
            self.current_effects.unknown_global = true;
        }
    }

    pub(crate) fn opaque_effects_in(&mut self, file: FileId, root: Root<'a>) -> bool {
        if self.fallback_active() || self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return true;
        }

        let kinds = self.counted_subtree(file, root, Event::EffectPrepassNode);

        if self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return true;
        }

        self.opaque_effects_of(file, kinds)
    }

    pub(crate) fn opaque_effects_at(&mut self, file: FileId, node: oxc_semantic::NodeId) -> bool {
        if self.fallback_active() || self.work_exhausted() {
            self.current_effects.unknown_global = true;

            return true;
        }

        let mut pending = vec![node];
        let mut kinds = Vec::new();

        while let Some(node) = pending.pop() {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                return true;
            }

            let kind = self.kind_of_node(file, node);

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                continue;
            }

            kinds.push(kind);
            pending.extend(self.children_of(file, node));
        }

        self.opaque_effects_of(file, kinds)
    }

    fn opaque_effects_of(&mut self, file: FileId, kinds: Vec<AstKind<'a>>) -> bool {
        for kind in kinds {
            if !self.charge_work(Event::EffectPrepassNode, 1) {
                return true;
            }

            if matches!(
                kind,
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                continue;
            }

            match kind {
                AstKind::AssignmentExpression(_) | AstKind::UpdateExpression(_) => {
                    self.record_write_effects(file, kind);
                }
                AstKind::CallExpression(call) => {
                    let declaration = self.callee_declaration_of(file, call);

                    if let Some(Declaration::Parameter { .. }) = declaration {
                        let facts = identifier_of(&call.callee)
                            .and_then(|reference| self.binding_of_identifier(file, reference))
                            .and_then(|binding| self.current_substitutions.get(&binding).cloned());

                        match facts {
                            Some(facts) => {
                                self.invoke_argument(&facts, file, call.span, &call.arguments);
                            }
                            None => return true,
                        }
                    } else if let Some((target, function)) = declaration
                        .and_then(|declaration| self.declarations.function_of(declaration))
                    {
                        self.call_user(target, function, file, &call.arguments, call.span);
                    } else {
                        self.current_effects.unknown_global = true;
                    }
                }
                AstKind::NewExpression(_) => self.current_effects.unknown_global = true,
                _ => {}
            }

            if self.current_effects.unknown_global {
                return true;
            }
        }

        self.current_effects.unknown_global
    }
}

impl Effects {
    pub fn unknown() -> Self {
        Self {
            unknown_global: true,
            ..Self::default()
        }
    }

    pub fn join(&mut self, other: &Self) {
        for binding in &other.binding_writes {
            if !self.binding_writes.contains(binding) {
                self.binding_writes.push(*binding);
            }
        }

        for (ours, theirs) in [
            (&mut self.member_writes, &other.member_writes),
            (&mut self.escapes, &other.escapes),
            (&mut self.unknown_reachable, &other.unknown_reachable),
        ] {
            for value in theirs {
                if !ours.contains(value) {
                    ours.push(*value);
                }
            }
        }

        self.unknown_global |= other.unknown_global;
    }
}
