use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Event {
    TaskKey,
    Publication,
    BodyPass,
    DependencyPair,
    DependencyWake,
    TraversalEdge,
    RuntimePair,
    InvocationSite,
    InvocationEvaluation,
    QueuePush,
    DiscoveryWave,
    CallbackDescriptor,
    CaptureEdge,
    WalkerNode,
    BudgetPrepassNode,
    EffectPrepassNode,
    GraphNode,
    GraphEdge,
    Specialization,
    RecurrenceContext,
    InvocationObservation,
    SemanticIdentity,
    DispatchStep,
    SizeStep,
    RecurrenceStep,
}

pub const EVENTS: [Event; 25] = [
    Event::TaskKey,
    Event::Publication,
    Event::BodyPass,
    Event::DependencyPair,
    Event::DependencyWake,
    Event::TraversalEdge,
    Event::RuntimePair,
    Event::InvocationSite,
    Event::InvocationEvaluation,
    Event::QueuePush,
    Event::DiscoveryWave,
    Event::CallbackDescriptor,
    Event::CaptureEdge,
    Event::WalkerNode,
    Event::BudgetPrepassNode,
    Event::EffectPrepassNode,
    Event::GraphNode,
    Event::GraphEdge,
    Event::Specialization,
    Event::RecurrenceContext,
    Event::InvocationObservation,
    Event::SemanticIdentity,
    Event::DispatchStep,
    Event::SizeStep,
    Event::RecurrenceStep,
];
const COUNT: usize = EVENTS.len();

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Charges([u64; COUNT]);

impl Charges {
    pub const ZERO: Self = Self([0; COUNT]);
    pub const fn one(event: Event, amount: u64) -> Self {
        let mut counts = [0; COUNT];
        counts[event as usize] = amount;

        Self(counts)
    }
    pub fn plus(mut self, event: Event, amount: u64) -> Result<Self, Rejection> {
        self.0[event as usize] = self.0[event as usize]
            .checked_add(amount)
            .ok_or(Rejection {
                event,
                reason: Reason::Overflow,
                requested: amount,
                available: u64::MAX - self.0[event as usize],
            })?;

        Ok(self)
    }
    pub const fn count(&self, event: Event) -> u64 {
        self.0[event as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Limits([u64; COUNT]);

impl Limits {
    pub const fn uniform(limit: u64) -> Self {
        Self([limit; COUNT])
    }
    pub fn with(mut self, event: Event, limit: u64) -> Self {
        self.0[event as usize] = limit;

        self
    }
    pub const fn limit(&self, event: Event) -> u64 {
        self.0[event as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    Limit,
    Overflow,
    ForeignCredit,
    ReleasedCredit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rejection {
    pub event: Event,
    pub reason: Reason,
    pub requested: u64,
    pub available: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Snapshot {
    ordinary: Charges,
    fallback: Charges,
    reserved: Charges,
    exhaustion: [bool; COUNT],
}

impl Snapshot {
    pub fn ordinary(&self) -> Charges {
        self.ordinary
    }
    pub fn fallback(&self) -> Charges {
        self.fallback
    }
    pub fn reserved(&self) -> Charges {
        self.reserved
    }
    pub fn consumed(&self, event: Event) -> u64 {
        self.ordinary.count(event) + self.fallback.count(event)
    }
    pub fn exhausted(&self, event: Event) -> bool {
        self.exhaustion[event as usize]
    }
}

pub struct WorkBudget {
    owner: Arc<()>,
    limits: Limits,
    snapshot: Snapshot,
}

pub struct FallbackCredit {
    owner: Arc<()>,
    remaining: Charges,
    released: bool,
}

impl FallbackCredit {
    pub fn remaining(&self) -> Charges {
        self.remaining
    }
}

impl WorkBudget {
    pub fn new(limits: Limits) -> Self {
        Self {
            owner: Arc::new(()),
            limits,
            snapshot: Snapshot {
                ordinary: Charges::ZERO,
                fallback: Charges::ZERO,
                reserved: Charges::ZERO,
                exhaustion: [false; COUNT],
            },
        }
    }

    pub fn snapshot(&self) -> Snapshot {
        self.snapshot
    }

    pub fn available(&self, event: Event) -> u64 {
        self.limits.limit(event)
            - self.snapshot.consumed(event)
            - self.snapshot.reserved.count(event)
    }

    fn check(&mut self, charges: Charges) -> Result<(), Rejection> {
        for event in EVENTS {
            let requested = charges.count(event);
            let available = self.available(event);

            if requested > available {
                self.snapshot.exhaustion[event as usize] = true;

                return Err(Rejection {
                    event,
                    reason: Reason::Limit,
                    requested,
                    available,
                });
            }
        }

        Ok(())
    }

    pub fn admit(&mut self, charges: Charges) -> Result<(), Rejection> {
        self.check(charges)?;

        for event in EVENTS {
            self.snapshot.ordinary.0[event as usize] += charges.count(event);
        }

        Ok(())
    }

    pub fn reserve_fallback(&mut self, charges: Charges) -> Result<FallbackCredit, Rejection> {
        self.check(charges)?;

        for event in EVENTS {
            self.snapshot.reserved.0[event as usize] += charges.count(event);
        }

        Ok(FallbackCredit {
            owner: Arc::clone(&self.owner),
            remaining: charges,
            released: false,
        })
    }

    pub fn admit_and_reserve(
        &mut self,
        ordinary: Charges,
        reserved: Charges,
    ) -> Result<FallbackCredit, Rejection> {
        let mut combined = ordinary;

        for event in EVENTS {
            combined = match combined.plus(event, reserved.count(event)) {
                Ok(combined) => combined,
                Err(error) => {
                    self.snapshot.exhaustion[event as usize] = true;

                    return Err(error);
                }
            };
        }

        self.check(combined)?;

        for event in EVENTS {
            self.snapshot.ordinary.0[event as usize] += ordinary.count(event);
            self.snapshot.reserved.0[event as usize] += reserved.count(event);
        }

        Ok(FallbackCredit {
            owner: Arc::clone(&self.owner),
            remaining: reserved,
            released: false,
        })
    }

    fn check_credit(&self, credit: &FallbackCredit) -> Result<(), Rejection> {
        let reason = if !Arc::ptr_eq(&self.owner, &credit.owner) {
            Some(Reason::ForeignCredit)
        } else if credit.released {
            Some(Reason::ReleasedCredit)
        } else {
            None
        };

        match reason {
            Some(reason) => Err(Rejection {
                event: Event::BodyPass,
                reason,
                requested: 0,
                available: 0,
            }),
            None => Ok(()),
        }
    }

    pub fn admit_fallback(
        &mut self,
        credit: &mut FallbackCredit,
        charges: Charges,
    ) -> Result<(), Rejection> {
        self.check_credit(credit)?;

        for event in EVENTS {
            let requested = charges.count(event);
            let available = credit.remaining.count(event);

            if requested > available {
                self.snapshot.exhaustion[event as usize] = true;

                return Err(Rejection {
                    event,
                    reason: Reason::Limit,
                    requested,
                    available,
                });
            }
        }

        for event in EVENTS {
            let amount = charges.count(event);
            credit.remaining.0[event as usize] -= amount;
            self.snapshot.reserved.0[event as usize] -= amount;
            self.snapshot.fallback.0[event as usize] += amount;
        }

        Ok(())
    }

    pub fn release(&mut self, credit: &mut FallbackCredit) -> Result<(), Rejection> {
        self.check_credit(credit)?;

        for event in EVENTS {
            self.snapshot.reserved.0[event as usize] -= credit.remaining.count(event);
        }

        credit.remaining = Charges::ZERO;
        credit.released = true;

        Ok(())
    }
}

#[cfg(test)]
#[path = "analysis_work.test.rs"]
mod tests;
