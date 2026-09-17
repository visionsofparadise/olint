use std::collections::HashMap;

use crate::cost::{Cost, Part, Preference};
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
}

impl Values {
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
