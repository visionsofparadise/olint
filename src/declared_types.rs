#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Kind {
    Array,
    Set,
    Map,
    String,
    RegExp,
    Other,
    #[default]
    Unknown,
}

impl Kind {
    pub fn rank(self) -> u8 {
        match self {
            Kind::Array => 6,
            Kind::Set | Kind::Map => 5,
            Kind::Unknown => 4,
            Kind::String => 3,
            Kind::RegExp => 2,
            Kind::Other => 1,
        }
    }

    pub fn join(self, other: Kind) -> Kind {
        if other.rank() > self.rank() {
            other
        } else {
            self
        }
    }
}
