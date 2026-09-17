use std::collections::HashMap;

use crate::cost::{Cost, CostError, Domain, Part, Preference};
use crate::declarations::TargetSet;
use crate::summaries::SummaryId;
use crate::unknowns::SourceSpan;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ValueId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SizeId {
    pub origin: SourceSpan,
    pub quantity: SizeQuantity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SizeQuantity {
    Length,
    Keys,
    Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueFacts {
    pub value: ValueId,
    pub size: Option<Cost>,
    pub targets: TargetSet,
    pub latent: Option<SummaryId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgumentFacts {
    pub value: ValueFacts,
    pub callback: Option<Part>,
    pub preference: Preference,
}

#[derive(Default)]
pub struct Values {
    origins: HashMap<SourceSpan, ValueId>,
    callbacks: HashMap<usize, ValueId>,
    next_value: u32,
    quantities: HashMap<(ValueId, SizeQuantity), u64>,
    labels: Vec<String>,
}

impl Values {
    pub fn quantity(
        &mut self,
        value: ValueId,
        quantity: SizeQuantity,
        label: String,
    ) -> Result<Cost, CostError> {
        let next = u64::try_from(self.labels.len()).map_err(|_| CostError::Resource)?;
        let id = *self.quantities.entry((value, quantity)).or_insert_with(|| {
            self.labels.push(label);

            next
        });

        Ok(Cost::dimension(id, Domain::Size))
    }

    pub fn label(&self, id: u64) -> String {
        if id == u64::MAX {
            return "N".into();
        }

        self.labels
            .get(id as usize)
            .cloned()
            .unwrap_or_else(|| format!("size_{id}"))
    }

    pub fn write_label(&self, id: u64, out: &mut dyn std::fmt::Write) -> std::fmt::Result {
        if id == u64::MAX {
            return out.write_str("N");
        }

        match self.labels.get(id as usize) {
            Some(label) => out.write_str(label),
            None => write!(out, "size_{id}"),
        }
    }

    pub fn prefer_length_label(&mut self, value: ValueId) {
        if let Some(id) = self.quantities.get(&(value, SizeQuantity::Value)) {
            let label = &mut self.labels[*id as usize];

            if !label.ends_with(".length") {
                label.push_str(".length");
            }
        }
    }

    pub(crate) fn callback(&mut self, descriptor: usize) -> ValueFacts {
        let value = if let Some(value) = self.callbacks.get(&descriptor) {
            *value
        } else {
            let value = ValueId(self.next_value);
            self.next_value = self
                .next_value
                .checked_add(1)
                .expect("callback value arena fits u32");

            self.callbacks.insert(descriptor, value);

            value
        };

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }

    pub fn at(&mut self, origin: SourceSpan) -> ValueFacts {
        let value = if let Some(value) = self.origins.get(&origin) {
            *value
        } else {
            let value = ValueId(self.next_value);
            self.next_value = self
                .next_value
                .checked_add(1)
                .expect("value arena fits u32");

            self.origins.insert(origin, value);

            value
        };

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }
}
