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

    pub fn prefer_length_label(&mut self, value: ValueId) {
        if let Some(id) = self.quantities.get(&(value, SizeQuantity::Value)) {
            let label = &mut self.labels[*id as usize];

            if !label.ends_with(".length") {
                label.push_str(".length");
            }
        }
    }

    pub fn at(&mut self, origin: SourceSpan) -> ValueFacts {
        let next = ValueId(u32::try_from(self.origins.len()).expect("value arena fits u32"));
        let value = *self.origins.entry(origin).or_insert(next);

        ValueFacts {
            value,
            size: None,
            targets: TargetSet::default(),
            latent: None,
        }
    }
}
