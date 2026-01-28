use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Attr {
    pub id: u128,
    pub ident: String,
    pub variety: Variety,
    pub uniqueness: Uniqueness,
    pub cardinality: Cardinality,
    pub commutative: bool,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Variety {
    #[default]
    Identity,
    Component,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Uniqueness {
    #[default]
    Unique,
    Common,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cardinality {
    pub lower: u32,
    pub upper: u32, // 0 = unbounded
}

impl Default for Cardinality {
    fn default() -> Self {
        Self { lower: 1, upper: 1 }
    }
}

impl Cardinality {
    pub const ONE: Self = Self { lower: 1, upper: 1 };
    pub const MANY: Self = Self { lower: 0, upper: 0 };
}

pub struct AttrStore {
    attrs: Vec<Attr>,
    index: HashMap<String, u32>,
}

impl AttrStore {
    pub fn new() -> Self {
        Self {
            attrs: Vec::new(),
            index: HashMap::new(),
        }
    }

    /// Get or create attr with default metadata, returns ref
    pub fn resolve(&mut self, ident: &str) -> u128 {
        if let Some(&idx) = self.index.get(ident) {
            return self.attrs[idx as usize].id;
        }

        let id = crate::ulid::id();
        let attr = Attr {
            id,
            ident: ident.to_string(),
            variety: Variety::default(),
            uniqueness: Uniqueness::default(),
            cardinality: Cardinality::default(),
            commutative: false,
        };

        self.insert(attr);
        id
    }

    /// Lookup by ident (read-only)
    pub fn lookup(&self, ident: &str) -> Option<&Attr> {
        self.index.get(ident).map(|&idx| &self.attrs[idx as usize])
    }

    /// Lookup by ref (binary search)
    pub fn get(&self, ref_: u128) -> Option<&Attr> {
        self.attrs
            .binary_search_by_key(&ref_, |a| a.id)
            .ok()
            .map(|idx| &self.attrs[idx])
    }

    /// Define attr with custom metadata
    pub fn define(&mut self, attr: Attr) -> Result<(), String> {
        if self.index.contains_key(&attr.ident) {
            return Err(format!("attribute already defined: {}", attr.ident));
        }
        if self.get(attr.id).is_some() {
            return Err(format!("ref already in use: {}", attr.id));
        }
        self.insert(attr);
        Ok(())
    }

    fn insert(&mut self, attr: Attr) {
        let pos = self
            .attrs
            .binary_search_by_key(&attr.id, |a| a.id)
            .unwrap_or_else(|pos| pos);

        // Update indices for shifted elements
        for idx in self.index.values_mut() {
            if *idx >= pos as u32 {
                *idx += 1;
            }
        }

        self.index.insert(attr.ident.clone(), pos as u32);
        self.attrs.insert(pos, attr);
    }

    pub fn clear(&mut self) {
        self.attrs.clear();
        self.index.clear();
    }
}

impl Default for AttrStore {
    fn default() -> Self {
        Self::new()
    }
}
