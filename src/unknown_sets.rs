use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SetId(u32);

impl SetId {
    pub const EMPTY: Self = Self(0);
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Resource,
    InvalidRoot,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub atoms: usize,
    pub nodes: usize,
    pub union_pairs: usize,
    pub work: u64,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Counts {
    pub atoms: usize,
    pub nodes: usize,
    pub edges: usize,
    pub union_pairs: usize,
    pub work: u64,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Branch {
    depth: u8,
    left: SetId,
    right: SetId,
}

pub struct Sets<A> {
    atoms: HashMap<A, u32>,
    nodes: Vec<Branch>,
    interned: HashMap<Branch, SetId>,
    unions: HashMap<(SetId, SetId), SetId>,
    limits: Limits,
    counts: Counts,
}

impl<A: Eq + Hash> Sets<A> {
    pub fn new(limits: Limits) -> Self {
        Self {
            atoms: HashMap::new(),
            nodes: Vec::new(),
            interned: HashMap::new(),
            unions: HashMap::new(),
            limits,
            counts: Counts::default(),
        }
    }

    pub fn counts(&self) -> Counts {
        self.counts
    }

    pub fn set_limits(&mut self, limits: Limits) -> Result<(), Error> {
        if limits.atoms < self.counts.atoms
            || limits.nodes < self.counts.nodes
            || limits.union_pairs < self.counts.union_pairs
            || limits.work < self.counts.work
        {
            return Err(Error::Resource);
        }

        self.limits = limits;

        Ok(())
    }

    fn charge(&mut self, work: &mut impl FnMut() -> bool) -> Result<(), Error> {
        if !work() {
            return Err(Error::Resource);
        }

        let next = self.counts.work.checked_add(1).ok_or(Error::Resource)?;

        if next > self.limits.work {
            return Err(Error::Resource);
        }

        self.counts.work = next;

        Ok(())
    }

    fn branch(&mut self, branch: Branch, work: &mut impl FnMut() -> bool) -> Result<SetId, Error> {
        self.charge(work)?;

        if let Some(id) = self.interned.get(&branch) {
            return Ok(*id);
        }

        if self.nodes.len() >= self.limits.nodes {
            return Err(Error::Resource);
        }

        let id = self.nodes.len().checked_add(2).ok_or(Error::Resource)?;
        let id = SetId(u32::try_from(id).map_err(|_| Error::Resource)?);
        let edges =
            usize::from(branch.left != SetId::EMPTY) + usize::from(branch.right != SetId::EMPTY);
        let total_edges = self
            .counts
            .edges
            .checked_add(edges)
            .ok_or(Error::Resource)?;

        self.nodes.push(branch);
        self.interned.insert(branch, id);

        self.counts.nodes = self.nodes.len();
        self.counts.edges = total_edges;

        Ok(id)
    }

    fn singleton_id(&mut self, atom: u32, work: &mut impl FnMut() -> bool) -> Result<SetId, Error> {
        let mut root = SetId(1);

        for depth in (0..32).rev() {
            let (left, right) = if atom & (1 << (31 - depth)) == 0 {
                (root, SetId::EMPTY)
            } else {
                (SetId::EMPTY, root)
            };
            root = self.branch(Branch { depth, left, right }, work)?;
        }

        Ok(root)
    }

    pub fn singleton(&mut self, atom: A, work: &mut impl FnMut() -> bool) -> Result<SetId, Error> {
        self.charge(work)?;

        let id = if let Some(id) = self.atoms.get(&atom) {
            *id
        } else {
            if self.atoms.len() >= self.limits.atoms {
                return Err(Error::Resource);
            }

            let id = u32::try_from(self.atoms.len()).map_err(|_| Error::Resource)?;

            self.atoms.insert(atom, id);

            self.counts.atoms = self.atoms.len();

            id
        };

        self.singleton_id(id, work)
    }

    fn valid_root(&self, root: SetId) -> bool {
        root == SetId::EMPTY
            || root
                .0
                .checked_sub(2)
                .and_then(|index| self.nodes.get(index as usize))
                .is_some_and(|branch| branch.depth == 0)
    }

    pub fn union(
        &mut self,
        left: SetId,
        right: SetId,
        work: &mut impl FnMut() -> bool,
    ) -> Result<SetId, Error> {
        if !self.valid_root(left) || !self.valid_root(right) {
            return Err(Error::InvalidRoot);
        }

        self.union_inner(left, right, work)
    }

    fn union_inner(
        &mut self,
        left: SetId,
        right: SetId,
        work: &mut impl FnMut() -> bool,
    ) -> Result<SetId, Error> {
        self.charge(work)?;

        if left == right || right == SetId::EMPTY {
            return Ok(left);
        }

        if left == SetId::EMPTY {
            return Ok(right);
        }

        let pair = if left.0 < right.0 {
            (left, right)
        } else {
            (right, left)
        };

        if let Some(id) = self.unions.get(&pair) {
            return Ok(*id);
        }

        if self.unions.len() >= self.limits.union_pairs {
            return Err(Error::Resource);
        }

        let first = self.nodes[(left.0 - 2) as usize];
        let second = self.nodes[(right.0 - 2) as usize];
        let a = self.union_inner(first.left, second.left, work)?;
        let b = self.union_inner(first.right, second.right, work)?;
        let result = self.branch(
            Branch {
                depth: first.depth,
                left: a,
                right: b,
            },
            work,
        )?;

        if self.unions.len() >= self.limits.union_pairs {
            return Err(Error::Resource);
        }

        self.unions.insert(pair, result);

        self.counts.union_pairs = self.unions.len();

        Ok(result)
    }
}

impl<A: Eq + Hash> Default for Sets<A> {
    fn default() -> Self {
        Self::new(Limits {
            atoms: 100_000,
            nodes: 2_000_000,
            union_pairs: 1_000_000,
            work: 20_000_000,
        })
    }
}
