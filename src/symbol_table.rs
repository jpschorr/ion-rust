use fxhash::FxBuildHasher;
use lasso::{Capacity, Rodeo};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::num::NonZeroUsize;
use std::ops::Range;
use std::sync::Arc;

use crate::constants::v1_0;
use crate::{Symbol, SymbolId};

pub trait SymbolLookup {
    /// If defined, returns the Symbol ID associated with the provided text.
    fn sid_for(&self, text: &str) -> Option<SymbolId>;

    /// If defined, returns the Symbol associated with the provided Symbol ID.
    fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol>;

    /// If defined, returns the text associated with the provided Symbol ID.
    fn text_for(&self, sid: SymbolId) -> Option<&str> {
        // If the SID is out of bounds, returns None
        self.symbol_for(sid)?
            // If the text is unknown, returns None
            .text()
    }

    /// Returns true if the provided symbol ID maps to an entry in the symbol table (i.e. it is in
    /// the range of known symbols: 0 to max_id)
    ///
    /// Note that a symbol ID can be valid but map to unknown text. If a symbol table contains
    /// a null or non-string value, that entry in the table will be defined but not have text
    /// associated with it.
    ///
    /// This method allows users to distinguish between a SID with unknown text and a SID that is
    /// invalid.
    fn sid_is_valid(&self, sid: SymbolId) -> bool {
        sid < self.len()
    }

    /// Returns the number of symbols defined in the table.
    fn len(&self) -> usize;
}

/// Stores mappings from Symbol IDs to text and vice-versa.
// SymbolTable instances always have at least system symbols; they are never empty.
#[allow(clippy::len_without_is_empty)]
pub struct SymbolTable {
    symbols_by_id: Vec<Symbol>,
    ids_by_text: HashMap<Symbol, SymbolId, FxBuildHasher>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    /// Constructs a new symbol table pre-populated with the system symbols defined in the spec.
    pub(crate) fn new() -> SymbolTable {
        let mut symbol_table = SymbolTable {
            symbols_by_id: Vec::with_capacity(v1_0::SYSTEM_SYMBOLS.len()),
            ids_by_text: HashMap::with_hasher(FxBuildHasher::default()),
        };
        symbol_table.initialize();
        symbol_table
    }

    // Interns the v1.0 system symbols
    pub(crate) fn initialize(&mut self) {
        for &text in v1_0::SYSTEM_SYMBOLS.iter() {
            self.intern_or_add_placeholder(text);
        }
    }

    pub(crate) fn reset(&mut self) {
        self.symbols_by_id.clear();
        self.ids_by_text.clear();
        self.initialize();
    }

    /// If `text` is already in the symbol table, returns the corresponding [SymbolId].
    /// Otherwise, adds `text` to the symbol table and returns the newly assigned [SymbolId].
    pub fn intern<A: AsRef<str>>(&mut self, text: A) -> SymbolId {
        let text = text.as_ref();
        // If the text is already in the symbol table, return the ID associated with it.
        if let Some(id) = self.ids_by_text.get(text) {
            return *id;
        }

        // Otherwise, intern it and return the new ID.
        let id = self.symbols_by_id.len();
        let arc: Arc<str> = Arc::from(text);
        let symbol = Symbol::shared(arc);
        self.symbols_by_id.push(symbol.clone());
        self.ids_by_text.insert(symbol, id);
        id
    }

    /// Assigns unknown text to the next available symbol ID. This is used when an Ion reader
    /// encounters null or non-string values in a stream's symbol table.
    pub(crate) fn add_placeholder(&mut self) -> SymbolId {
        let sid = self.symbols_by_id.len();
        self.symbols_by_id.push(Symbol::unknown_text());
        sid
    }

    /// If `maybe_text` is `Some(text)`, this method is equivalent to `intern(text)`.
    /// If `maybe_text` is `None`, this method is equivalent to `add_placeholder()`.
    pub(crate) fn intern_or_add_placeholder<A: AsRef<str>>(
        &mut self,
        maybe_text: Option<A>,
    ) -> SymbolId {
        match maybe_text {
            Some(text) => self.intern(text),
            None => self.add_placeholder(),
        }
    }

    /// Returns a slice of references to the symbol text stored in the table starting at the given
    /// symbol ID. If a symbol table append occurs during reading, this function can be used to
    /// easily view the new symbols that has been added to the table.
    ///
    /// The symbol table can contain symbols with unknown text; see the documentation for
    /// [Symbol] for more information.
    // TODO: Is this necessary vs just taking a slice of the `symbols()` method above?
    pub(crate) fn symbols_tail(&self, start: usize) -> &[Symbol] {
        &self.symbols_by_id[start..]
    }

    /// Returns a slice of references to the symbol text stored in the table.
    ///
    /// The symbol table can contain symbols with unknown text; see the documentation for
    /// [Symbol] for more information.
    fn symbols(&self) -> &[Symbol] {
        &self.symbols_by_id
    }
}

impl SymbolLookup for SymbolTable {
    /// If defined, returns the Symbol ID associated with the provided text.
    fn sid_for(&self, text: &str) -> Option<SymbolId> {
        self.ids_by_text.get(text).copied()
    }

    /// If defined, returns the Symbol associated with the provided Symbol ID.
    fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        self.symbols_by_id.get(sid)
    }

    /// If defined, returns the text associated with the provided Symbol ID.
    fn text_for(&self, sid: SymbolId) -> Option<&str> {
        self.symbols_by_id
            // If the SID is out of bounds, returns None
            .get(sid)?
            // If the text is unknown, returns None
            .text()
    }

    /// Returns true if the provided symbol ID maps to an entry in the symbol table (i.e. it is in
    /// the range of known symbols: 0 to max_id)
    ///
    /// Note that a symbol ID can be valid but map to unknown text. If a symbol table contains
    /// a null or non-string value, that entry in the table will be defined but not have text
    /// associated with it.
    ///
    /// This method allows users to distinguish between a SID with unknown text and a SID that is
    /// invalid.
    fn sid_is_valid(&self, sid: SymbolId) -> bool {
        sid < self.symbols_by_id.len()
    }

    /// Returns the number of symbols defined in the table.
    fn len(&self) -> usize {
        self.symbols_by_id.len()
    }
}

pub type SymId = NonZeroUsize;
type IdIndex = usize;
type ByteIndex = usize;

#[derive(Clone)]
pub struct SymbolArena<'data> {
    arena: String,
    ids: Vec<Range<ByteIndex>>,
    mapping: HashMap<&'data str, SymId>,
}

impl<'data> Default for SymbolArena<'data> {
    fn default() -> Self {
        SymbolArena::new()
    }
}

impl<'data> SymbolArena<'data> {
    pub fn new() -> Self {
        let mut st = SymbolArena {
            arena: String::with_capacity(200),
            ids: vec![],
            mapping: Default::default(),
        };
        st.initialize()
    }
    // Interns the v1.0 system symbols
    pub(crate) fn initialize(mut self) -> Self {
        for &text in v1_0::SYSTEM_SYMBOLS.iter() {
            if let Some(text) = text {
                (self, _) = self.intern(text);
            }
        }
        self
    }

    pub(crate) fn reset(mut self) -> Self {
        self.arena.clear();
        self.ids.clear();
        self.mapping.clear();
        self.initialize()
    }

    pub fn len(&self) -> usize {
        self.ids.len()
    }

    pub fn find_or_intern<'new>(self: SymbolArena<'data>, txt: &str) -> (SymbolArena<'new>, SymId) {
        if let Some(id) = self.find(txt) {
            (unsafe { std::mem::transmute(self) }, id)
        } else {
            self.intern(txt)
        }
    }

    #[inline(always)]
    pub fn intern<'new>(self: SymbolArena<'data>, txt: &str) -> (SymbolArena<'new>, SymId) {
        let bump = self.arena.capacity() < self.arena.len() + txt.len();
        //if bump {
        //    dbg!(&self.mapping);
        //}
        let SymbolArena {
            mut arena,
            mut ids,
            mut mapping,
        } = self;

        let start = arena.len();
        arena.push_str(txt);
        let extent = arena.len();

        ids.push(start..extent);
        let id = unsafe { NonZeroUsize::new_unchecked(ids.len()) };

        let id = if bump {
            mapping.clear();
            let mut id = unsafe { NonZeroUsize::new_unchecked(1) };
            for (idx, span) in ids.iter().enumerate() {
                let new_id = unsafe { NonZeroUsize::new_unchecked(idx + 1) };
                let txt = unsafe { std::mem::transmute(&arena[span.start..span.end]) };
                id = *mapping.entry(txt).or_insert(new_id);
            }
            id
        } else {
            let txt = unsafe { std::mem::transmute(&arena[start..extent]) };
            *mapping.entry(txt).or_insert(id)
        };

        //if bump {
        //    dbg!(&mapping);
        //}
        //dbg!(&mapping);
        let new: SymbolArena<'new> = SymbolArena {
            arena,
            ids,
            mapping: unsafe { std::mem::transmute(mapping) },
        };
        (new, id)
    }

    pub fn intern_empty<'new>(self: SymbolArena<'data>) -> (SymbolArena<'new>, SymId) {
        let SymbolArena {
            mut arena,
            mut ids,
            mut mapping,
        } = self;
        let start = arena.len();

        ids.push(start..start);
        let id = unsafe { NonZeroUsize::new_unchecked(ids.len()) };

        let new: SymbolArena<'new> = SymbolArena {
            arena,
            ids,
            mapping: unsafe { std::mem::transmute(mapping) },
        };
        (new, id)
    }

    #[inline]
    pub fn get(&'data self, id: SymId) -> Option<&'data str> {
        let range = self.ids.get(id.get() - 1)?;
        if range.is_empty() {
            None
        } else {
            Some(unsafe { self.arena.get_unchecked(range.start..range.end) })
        }
    }

    pub fn find(&'data self, txt: &str) -> Option<SymId> {
        //if txt == "bar10" {
        // dbg!(&self);
        //}
        self.mapping.get(txt).copied()
    }

    pub fn dump(&self) {
        dbg!(&self.mapping);
    }
}

impl<'data> Debug for SymbolArena<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut container = f.debug_struct("Symbols");
        for id in 0..=self.len() {
            let txt = self.text_for(id);
            container.field(&format!("{}", id), &txt);
        }
        container.finish()?;

        Ok(())
    }
}

impl<'data> SymbolLookup for SymbolArena<'data> {
    fn sid_for(&self, text: &str) -> Option<SymbolId> {
        self.find(text).map(|s| s.get())
    }

    fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        todo!()
    }

    #[inline]
    fn text_for(&self, sid: SymbolId) -> Option<&str> {
        //NonZeroUsize::new(sid).and_then(|sym| self.get(sym))
        self.get(NonZeroUsize::new(sid)?)
        //let range = self.ids.get(sid)?;
        //Some(unsafe { self.arena.get_unchecked(range.start..range.end) })
        //Some(&self.arena[range.start..range.end])
    }

    fn len(&self) -> usize {
        self.len()
    }
}

#[derive(Clone)]
pub struct SymbolRefTable<'data> {
    ids: Vec<&'data str>,
    mapping: HashMap<&'data str, SymId>,
}

impl<'data> Default for SymbolRefTable<'data> {
    fn default() -> Self {
        SymbolRefTable::new()
    }
}

impl<'data> SymbolRefTable<'data> {
    pub fn new() -> Self {
        let mut st = SymbolRefTable {
            ids: vec![],
            mapping: Default::default(),
        };
        st.initialize()
    }
    // Interns the v1.0 system symbols
    pub(crate) fn initialize(mut self) -> Self {
        for &text in v1_0::SYSTEM_SYMBOLS.iter() {
            if let Some(text) = text {
                self.intern(text);
            }
        }
        self
    }

    pub(crate) fn reset(mut self) -> Self {
        self.ids.clear();
        self.mapping.clear();
        self.initialize()
    }

    pub fn len(&self) -> usize {
        self.ids.len()
    }

    pub fn find_or_intern(&mut self, txt: &'data str) -> SymId {
        self.find(txt).unwrap_or_else(|| self.intern(txt))
    }

    pub fn intern(&mut self, txt: &'data str) -> SymId {
        self.ids.push(txt);
        let id = unsafe { NonZeroUsize::new_unchecked(self.ids.len()) };
        let id = self.mapping.entry(txt).or_insert(id);

        *id
    }

    pub fn intern_empty(&mut self) -> SymId {
        self.intern("")
    }

    #[inline]
    pub fn get(&'data self, id: SymId) -> Option<&'data str> {
        self.ids.get(id.get() - 1).copied()
    }

    pub fn find(&'data self, txt: &str) -> Option<SymId> {
        self.mapping.get(txt).copied()
    }
}

impl<'data> Debug for SymbolRefTable<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut container = f.debug_struct("Symbols");
        for id in 0..=self.len() {
            let txt = self.text_for(id);
            container.field(&format!("{}", id), &txt);
        }
        container.finish()?;

        Ok(())
    }
}

impl<'data> SymbolLookup for SymbolRefTable<'data> {
    fn sid_for(&self, text: &str) -> Option<SymbolId> {
        self.find(text.as_ref()).map(|s| s.get())
    }

    fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        todo!()
    }

    #[inline]
    fn text_for(&self, sid: SymbolId) -> Option<&str> {
        //NonZeroUsize::new(sid).and_then(|sym| self.get(sym))
        self.get(NonZeroUsize::new(sid)?)
        //let range = self.ids.get(sid)?;
        //Some(unsafe { self.arena.get_unchecked(range.start..range.end) })
        //Some(&self.arena[range.start..range.end])
    }

    fn len(&self) -> usize {
        self.len()
    }
}

#[derive(Clone)]
pub struct LassoTable {
    ids: Vec<lasso::LargeSpur>,
    rodeo: Rodeo<lasso::LargeSpur, FxBuildHasher>,
}

impl Default for LassoTable {
    fn default() -> Self {
        LassoTable::new()
    }
}

impl LassoTable {
    pub fn new() -> Self {
        let mut st = LassoTable {
            ids: Default::default(),
            rodeo: Rodeo::with_hasher(FxBuildHasher::default()),
            //ids: Vec::with_capacity(1300),
            //rodeo: Rodeo::with_capacity_and_hasher(
            //    Capacity::new(1300, NonZeroUsize::new(1300 * 6).unwrap()),
            //    FxBuildHasher::default(),
            //),
        };
        st.initialize()
    }
    // Interns the v1.0 system symbols
    pub(crate) fn initialize(mut self) -> Self {
        for &text in v1_0::SYSTEM_SYMBOLS.iter() {
            if let Some(text) = text {
                self.intern(text);
            }
        }
        self
    }

    pub(crate) fn reset(mut self) -> Self {
        self.ids.clear();
        self.rodeo.clear();
        self.initialize()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    pub fn intern(&mut self, txt: &str) -> SymId {
        let key = self.rodeo.get_or_intern(txt);
        self.ids.push(key);
        key.into_inner()
    }

    pub fn intern_empty(&mut self) -> SymId {
        self.intern("")
    }

    #[inline]
    pub fn get(&self, id: SymId) -> Option<&str> {
        //self.rodeo.try_resolve(self.ids.get(id.get() - 1)?)

        self.ids.get(id.get() - 1).map(|k| self.rodeo.resolve(k))
    }

    #[inline]
    pub fn find(&self, txt: &str) -> Option<SymId> {
        self.rodeo.get(txt).map(|spur| spur.into_inner())
    }
}

impl Debug for LassoTable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut container = f.debug_struct("Symbols");
        for id in 0..=self.len() {
            let txt = self.text_for(id);
            container.field(&format!("{}", id), &txt);
        }
        container.finish()?;

        Ok(())
    }
}

impl SymbolLookup for LassoTable {
    #[inline]
    fn sid_for(&self, text: &str) -> Option<SymbolId> {
        self.find(text).map(|s| s.get())
    }

    fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
        todo!()
    }

    #[inline]
    fn text_for(&self, sid: SymbolId) -> Option<&str> {
        //NonZeroUsize::new(sid).and_then(|sym| self.get(sym))
        self.get(NonZeroUsize::new(sid)?)
        //let range = self.ids.get(sid)?;
        //Some(unsafe { self.arena.get_unchecked(range.start..range.end) })
        //Some(&self.arena[range.start..range.end])
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }
}
