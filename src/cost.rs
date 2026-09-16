use crate::project::Site;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Cost {
    pub n: u32,
    pub log: u32,
}

impl Cost {
    pub const ONE: Cost = Cost { n: 0, log: 0 };
    pub const N: Cost = Cost { n: 1, log: 0 };
    pub const LOG: Cost = Cost { n: 0, log: 1 };
    pub const N_LOG_N: Cost = Cost { n: 1, log: 1 };

    pub fn is_one(self) -> bool {
        self.n == 0 && self.log == 0
    }

    pub fn multiply(self, other: Cost) -> Cost {
        Cost {
            n: self.n + other.n,
            log: self.log + other.log,
        }
    }

    pub fn exceeds(self, other: Cost) -> bool {
        if self.n != other.n {
            self.n > other.n
        } else {
            self.log > other.log
        }
    }

    pub fn text(self) -> String {
        if self.is_one() {
            return "O(1)".to_string();
        }

        let linear = match self.n {
            0 => String::new(),
            1 => "N".to_string(),
            power => format!("N^{power}"),
        };
        let logarithm = match self.log {
            0 => String::new(),
            1 => "log N".to_string(),
            power => format!("log^{power} N"),
        };
        let parts: Vec<String> = [linear, logarithm]
            .into_iter()
            .filter(|part| !part.is_empty())
            .collect();

        format!("O({})", parts.join(" "))
    }

    pub fn parse(text: &str) -> Option<Cost> {
        let compact: String = text
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        let inner = compact.strip_prefix("O(")?.strip_suffix(')')?;

        if inner == "1" {
            return Some(Cost::ONE);
        }

        if inner == "logN" {
            return Some(Cost::LOG);
        }

        let after_linear = inner.strip_prefix('N')?;
        let (power_text, log) = match after_linear.strip_suffix("logN") {
            Some(rest) => (rest, 1),
            None => (after_linear, 0),
        };
        let n = if power_text.is_empty() {
            1
        } else {
            let digits = power_text.strip_prefix('^')?;

            if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
                return None;
            }

            digits.parse().ok()?
        };

        Some(Cost { n, log })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factor {
    pub label: String,
    pub site: Site,
    pub cost: Cost,
    pub inner: Vec<Factor>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Preference {
    #[default]
    Absent,
    Cold,
    Unmarked,
    Hot,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Part {
    pub cost: Cost,
    pub chain: Vec<Factor>,
    pub preference: Preference,
}

impl Part {
    pub fn none() -> Part {
        Part::default()
    }

    pub fn unmarked(cost: Cost, chain: Vec<Factor>) -> Part {
        Part {
            cost,
            chain,
            preference: Preference::Unmarked,
        }
    }

    fn rank(&self) -> u8 {
        match self.preference {
            Preference::Absent if self.cost.is_one() => 0,
            Preference::Cold => 1,
            Preference::Absent | Preference::Unmarked => 2,
            Preference::Hot => 3,
        }
    }

    pub fn max(self, other: Part) -> Part {
        let (mine, theirs) = (self.rank(), other.rank());

        if theirs > mine || (theirs == mine && other.cost.exceeds(self.cost)) {
            other
        } else {
            self
        }
    }

    pub fn preferred(self, preference: Preference) -> Part {
        Part { preference, ..self }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reading {
    pub main: Part,
    pub function_exit: Part,
    pub loop_exit: Part,
}

impl Reading {
    pub fn empty() -> Reading {
        Reading::default()
    }

    pub fn of_part(part: Part) -> Reading {
        Reading {
            main: part,
            function_exit: Part::none(),
            loop_exit: Part::none(),
        }
    }

    pub fn merge(self, other: Reading) -> Reading {
        Reading {
            main: self.main.max(other.main),
            function_exit: self.function_exit.max(other.function_exit),
            loop_exit: self.loop_exit.max(other.loop_exit),
        }
    }

    pub fn preferred(self, preference: Preference) -> Reading {
        let exit = |part: Part| {
            if part.preference == Preference::Absent && part.cost.is_one() {
                part
            } else {
                part.preferred(preference)
            }
        };

        Reading {
            main: self.main.preferred(preference),
            function_exit: exit(self.function_exit),
            loop_exit: exit(self.loop_exit),
        }
    }

    pub fn sibling(self) -> Reading {
        if self.main.preference != Preference::Absent {
            return self;
        }

        Reading {
            main: self.main.preferred(Preference::Unmarked),
            ..self
        }
    }

    pub fn total(&self) -> Part {
        self.main
            .clone()
            .max(self.function_exit.clone())
            .max(self.loop_exit.clone())
    }
}

pub fn nest(label: String, site: Site, factor: Cost, inner: Part) -> Part {
    let mut chain = Vec::with_capacity(inner.chain.len() + 1);

    chain.push(Factor {
        label,
        site,
        cost: factor,
        inner: Vec::new(),
    });
    chain.extend(inner.chain);

    Part {
        cost: factor.multiply(inner.cost),
        chain,
        preference: if inner.preference == Preference::Absent {
            Preference::Unmarked
        } else {
            inner.preference
        },
    }
}

#[cfg(test)]
#[path = "cost.test.rs"]
mod tests;
