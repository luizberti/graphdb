//! Attribute definitions with schema metadata

use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Attr {
    pub ref_: u128,
    pub ident: String,
    pub variety: Variety,
    pub uniqueness: Uniqueness,
    pub commutative: bool,
    pub cardinality: Cardinality,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Variety {
    #[default]
    Component,
    Identity,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Uniqueness {
    Unique,
    #[default]
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
    ident_index: HashMap<String, u32>,
}

impl AttrStore {
    pub fn new() -> Self {
        Self {
            attrs: Vec::new(),
            ident_index: HashMap::new(),
        }
    }

    /// Get or create attr with default metadata, returns ref
    pub fn resolve(&mut self, ident: &str) -> u128 {
        if let Some(&idx) = self.ident_index.get(ident) {
            return self.attrs[idx as usize].ref_;
        }

        let ref_ = crate::ulid::id();
        let attr = Attr {
            ref_,
            ident: ident.to_string(),
            variety: Variety::default(),
            uniqueness: Uniqueness::default(),
            commutative: false,
            cardinality: Cardinality::default(),
        };

        self.insert(attr);
        ref_
    }

    /// Lookup by ident (read-only)
    pub fn lookup(&self, ident: &str) -> Option<&Attr> {
        self.ident_index
            .get(ident)
            .map(|&idx| &self.attrs[idx as usize])
    }

    /// Lookup by ref (binary search)
    pub fn get(&self, ref_: u128) -> Option<&Attr> {
        self.attrs
            .binary_search_by_key(&ref_, |a| a.ref_)
            .ok()
            .map(|idx| &self.attrs[idx])
    }

    /// Define attr with custom metadata
    pub fn define(&mut self, attr: Attr) -> Result<(), String> {
        if self.ident_index.contains_key(&attr.ident) {
            return Err(format!("attribute already defined: {}", attr.ident));
        }
        if self.get(attr.ref_).is_some() {
            return Err(format!("ref already in use: {}", attr.ref_));
        }
        self.insert(attr);
        Ok(())
    }

    fn insert(&mut self, attr: Attr) {
        let pos = self
            .attrs
            .binary_search_by_key(&attr.ref_, |a| a.ref_)
            .unwrap_or_else(|pos| pos);

        // Update indices for shifted elements
        for idx in self.ident_index.values_mut() {
            if *idx >= pos as u32 {
                *idx += 1;
            }
        }

        self.ident_index.insert(attr.ident.clone(), pos as u32);
        self.attrs.insert(pos, attr);
    }

    pub fn clear(&mut self) {
        self.attrs.clear();
        self.ident_index.clear();
    }
}

impl Default for AttrStore {
    fn default() -> Self {
        Self::new()
    }
}
