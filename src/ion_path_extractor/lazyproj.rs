// Copyright Amazon.com, Inc. or its affiliates.

use crate::constants::v1_0;
use crate::constants::v1_0::system_symbol_ids::{IMPORTS, ION_SYMBOL_TABLE, SYMBOLS};
use crate::lazy::binary::raw::r#struct::LazyRawBinaryField;
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::value::ValueParseResult;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    AnnotationsMatch, LazyDecoder, LazyRawAnnotated, LazyRawSequence, LazyRawTyped, LazyRawValue,
};
use crate::lazy::decoder::{LazyRawReader, LazyRawStruct};
use crate::lazy::encoding::BinaryEncoding;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::reader::LazyReader;
use crate::lazy::str_ref::StrRef;
use crate::lazy::system_reader::LazySystemReader;
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::value::LazyValue;
use crate::result::IonFailure;
use crate::symbol_table::{SymId, SymbolLookup};
use crate::{
    IonResult, IonType, LassoTable, RawSymbolTokenRef, Symbol, SymbolArena, SymbolId, SymbolTable,
};
use logos::Logos;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Debug, Display, Formatter, Pointer};
use std::num::NonZeroUsize;
use std::ops::Range;

#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")] // Ignore this regex pattern between tokens
enum Token {
    // Tokens can be literal strings, of any length.
    #[token("fast")]
    Fast,

    #[token(".")]
    Period,

    // Or regular expressions.
    #[regex("[a-zA-Z]+")]
    Text,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct PathId(usize);

pub(crate) trait AnnotToken:
    Sized + Display + Clone + PartialEq + Eq + PartialOrd + Ord
{
}
impl AnnotToken for String {}
impl AnnotToken for SymId {}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub(crate) enum SeqAction {
    // TODO Reject, ??
    Accept { path: PathId },
    Skip { n: usize },
    StepIn,
}
impl Debug for SeqAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SeqAction::Accept { path } => write!(f, "Accept({})", path.0),
            SeqAction::Skip { n } => write!(f, "Skip({})", n),
            SeqAction::StepIn => write!(f, "StepIn"),
        }
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub(crate) enum StructAction {
    // TODO Reject, ??
    Accept { path: PathId },
    StepIn,
}
impl Debug for StructAction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StructAction::Accept { path } => write!(f, "Accept({})", path.0),
            StructAction::StepIn => write!(f, "StepIn"),
        }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) struct AnnotMatch<T: AnnotToken> {
    annot: Vec<T>,
}
impl<T: AnnotToken> Debug for AnnotMatch<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for annot in &self.annot {
            write!(f, "{}::", annot)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub(crate) enum SeqValMatch {
    Any,
    Index { n: usize },
}
impl Debug for SeqValMatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SeqValMatch::Any => write!(f, "*"),
            SeqValMatch::Index { n } => write!(f, "n"),
        }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) enum StructValMatch<T: AnnotToken> {
    Any,
    Field { name: T },
}
impl<T: AnnotToken> Debug for StructValMatch<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StructValMatch::Any => write!(f, "*"),
            StructValMatch::Field { name } => write!(f, "{}", name),
        }
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub(crate) enum TypeMatch {
    Struct,
    Seq,
}

impl Debug for TypeMatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeMatch::Struct => write!(f, ": {{}}"),
            TypeMatch::Seq => write!(f, ": []"),
        }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) struct SeqMatch<T: AnnotToken> {
    annot: Option<AnnotMatch<T>>,
    typ: Option<TypeMatch>,
    value: SeqValMatch,
}

impl<T: AnnotToken> Debug for SeqMatch<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        if let Some(annot) = &self.annot {
            annot.fmt(f)?;
        }
        self.value.fmt(f)?;
        if let Some(typ) = &self.typ {
            typ.fmt(f)?;
        }
        write!(f, "]")
    }
}

impl<T: AnnotToken> SeqMatch<T> {
    pub fn new(annot: Option<AnnotMatch<T>>, typ: Option<TypeMatch>, value: SeqValMatch) -> Self {
        Self { annot, typ, value }
    }

    pub fn any() -> Self {
        Self::new(None, None, SeqValMatch::Any)
    }

    pub fn typed(mut self, typ: TypeMatch) -> Self {
        self.typ = Some(typ);
        self
    }

    pub fn any_of_type(typ: TypeMatch) -> Self {
        Self::new(None, Some(typ), SeqValMatch::Any)
    }

    fn keys(&self) -> BTreeSet<&T> {
        match &self.annot {
            Some(a) => a.annot.iter().collect(),
            None => BTreeSet::default(),
        }
    }

    pub fn compile<U: AnnotToken>(&self, symtab: &BTreeMap<T, U>) -> SeqMatch<U> {
        let annot = self.annot.as_ref().map(|a| {
            let annot = a
                .annot
                .iter()
                .map(|a| symtab.get(a).unwrap().clone())
                .collect();
            AnnotMatch { annot }
        });
        let typ = self.typ.clone();
        let value = self.value.clone();
        SeqMatch { annot, typ, value }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) struct StructMatch<T: AnnotToken> {
    annot: Option<AnnotMatch<T>>,
    typ: Option<TypeMatch>,
    value: StructValMatch<T>,
}

impl<T: AnnotToken> Debug for StructMatch<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, ".")?;
        if let Some(annot) = &self.annot {
            annot.fmt(f)?;
        }
        self.value.fmt(f)?;
        if let Some(typ) = &self.typ {
            typ.fmt(f)?;
        }
        Ok(())
    }
}

impl<T: AnnotToken> StructMatch<T> {
    pub fn new(
        annot: Option<AnnotMatch<T>>,
        typ: Option<TypeMatch>,
        value: StructValMatch<T>,
    ) -> Self {
        Self { annot, typ, value }
    }

    pub fn any() -> Self {
        Self::new(None, None, StructValMatch::Any)
    }

    pub fn typed(mut self, typ: TypeMatch) -> Self {
        self.typ = Some(typ);
        self
    }

    pub fn any_of_type(typ: TypeMatch) -> Self {
        Self::new(None, Some(typ), StructValMatch::Any)
    }

    fn keys(&self) -> BTreeSet<&T> {
        let mut keys = match &self.annot {
            Some(a) => a.annot.iter().collect(),
            None => BTreeSet::default(),
        };
        match &self.value {
            StructValMatch::Field { name } => {
                keys.insert(name);
            }
            _ => {}
        }
        keys
    }

    pub fn compile<U: AnnotToken>(&self, symtab: &BTreeMap<T, U>) -> StructMatch<U> {
        let annot = self.annot.as_ref().map(|a| {
            let annot = a
                .annot
                .iter()
                .map(|a| symtab.get(a).unwrap().clone())
                .collect();
            AnnotMatch { annot }
        });
        let typ = self.typ.clone();
        let value = match &self.value {
            StructValMatch::Field { name } => StructValMatch::Field {
                name: symtab.get(name).unwrap().clone(),
            },
            StructValMatch::Any => StructValMatch::Any,
        };
        StructMatch { annot, typ, value }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) enum StepMatch<T: AnnotToken> {
    TopLevel(SeqMatch<T>),
    Seq(SeqMatch<T>),
    Struct(StructMatch<T>),
    Accept(PathId),
}
impl<T: AnnotToken> Debug for StepMatch<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StepMatch::TopLevel(mt) => {
                write!(f, "_")?;
                mt.fmt(f)?;
                write!(f, "_")
            }
            StepMatch::Seq(mt) => mt.fmt(f),
            StepMatch::Struct(mt) => mt.fmt(f),
            StepMatch::Accept(p) => write!(f, "Accept({})", p.0),
        }
    }
}
impl<T: AnnotToken> StepMatch<T> {
    fn keys(&self) -> BTreeSet<&T> {
        match self {
            StepMatch::TopLevel(mt) => mt.keys(),
            StepMatch::Seq(mt) => mt.keys(),
            StepMatch::Struct(mt) => mt.keys(),
            StepMatch::Accept(p) => BTreeSet::default(),
        }
    }

    pub fn compile<U: AnnotToken>(&self, symtab: &BTreeMap<T, U>) -> StepMatch<U> {
        match self {
            StepMatch::TopLevel(mt) => StepMatch::TopLevel(mt.compile(symtab)),
            StepMatch::Seq(mt) => StepMatch::Seq(mt.compile(symtab)),
            StepMatch::Struct(mt) => StepMatch::Struct(mt.compile(symtab)),
            StepMatch::Accept(p) => StepMatch::Accept(p.clone()),
        }
    }
}

impl<T: AnnotToken> From<SeqMatch<T>> for StepMatch<T> {
    fn from(value: SeqMatch<T>) -> Self {
        StepMatch::Seq(value)
    }
}

impl<T: AnnotToken> From<StructMatch<T>> for StepMatch<T> {
    fn from(value: StructMatch<T>) -> Self {
        StepMatch::Struct(value)
    }
}

impl<T: AnnotToken> From<PathId> for StepMatch<T> {
    fn from(value: PathId) -> Self {
        StepMatch::Accept(value)
    }
}

pub(crate) type StepPath<T: AnnotToken> = Vec<StepMatch<T>>;
pub(crate) type StepPathRef<'a, T: AnnotToken> = &'a [StepMatch<T>];
pub(crate) type StepChoices<T: AnnotToken> = Vec<StepMatch<T>>;

#[derive(Clone, Hash, Eq, PartialEq)]
pub(crate) struct Step<T: AnnotToken> {
    matches: Vec<(StepMatch<T>, Step<T>)>,
}

impl<T: AnnotToken> Default for Step<T> {
    fn default() -> Self {
        Self { matches: vec![] }
    }
}

impl<T: AnnotToken> Debug for Step<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for m in &self.matches {
            m.fmt(f)?;
        }
        Ok(())
    }
}

impl<T: AnnotToken> Step<T> {
    pub fn add_path(&mut self, path: StepPathRef<T>) {
        if let Some((head, tail)) = path.split_first() {
            if let Some((_, step)) = self.matches.iter_mut().find(|(cond, _)| cond == head) {
                step.add_path(tail);
            } else {
                let mut step = Step::default();
                step.add_path(tail);
                self.matches.push((head.clone(), step));
            }
        }
    }

    pub fn keys(&self) -> BTreeSet<&T> {
        let mut keys = BTreeSet::default();
        for (m, step) in &self.matches {
            keys.extend(m.keys());
            keys.extend(step.keys());
        }
        keys
    }

    pub fn compile<U: AnnotToken>(&self, symtab: &BTreeMap<T, U>) -> Step<U> {
        let matches = self
            .matches
            .iter()
            .map(|(m, step)| (m.compile(symtab), step.compile(symtab)))
            .collect();
        Step { matches }
    }
}

// Symbol IDs used for processing symbol table structs
const SYMREF_ION_SYMBOL_TABLE: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(ION_SYMBOL_TABLE);
const SYMREF_IMPORTS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(IMPORTS);
const SYMREF_SYMBOLS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(SYMBOLS);

#[derive(Debug)]
pub struct LZPSymbolTableUpdate<'data, D: LazyDecoder<'data>> {
    action: LZPSymbolTableUpdateAction,
    imports: Option<D::Sequence>,
    symbols: Option<D::Sequence>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum LZPSymbolTableUpdateAction {
    Append,
    Reset,
}

#[derive(Debug)]
/// Raw stream components that a RawReader may encounter.
pub enum LZPStreamItem<'data, D: LazyDecoder<'data>> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),

    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue).
    Value(D::Value),

    SymbolTableUpdate(LZPSymbolTableUpdate<'data, D>),

    /// The end of the stream
    EndOfStream,
}

pub struct LZPReader<'data, D: LazyDecoder<'data>> {
    raw_reader: D::Reader,
}
pub type LZPBinaryReader<'data> = LZPReader<'data, BinaryEncoding>;

impl<'data> LZPBinaryReader<'data> {
    pub(crate) fn new(ion_data: &'data [u8]) -> LZPBinaryReader<'data> {
        let raw_reader = LazyRawBinaryReader::new(ion_data);
        LZPBinaryReader { raw_reader }
    }
}

impl<'data, D: LazyDecoder<'data>> LZPReader<'data, D> {
    pub fn next<'top>(&'top mut self) -> IonResult<LZPStreamItem<'data, D>> {
        //-> IonResult<Option<LazyValue<'top, 'data, D, SymbolArena<'data>>>> {
        Ok(match self.raw_reader.next()? {
            RawStreamItem::VersionMarker(x, y) => LZPStreamItem::VersionMarker(x, y),
            RawStreamItem::Value(lazy_raw_value) => {
                match Self::maybe_symbol_table(lazy_raw_value)? {
                    Ok(symtab) => LZPStreamItem::SymbolTableUpdate(symtab),
                    Err(value) => LZPStreamItem::Value(value),
                }
            }
            RawStreamItem::EndOfStream => LZPStreamItem::EndOfStream,
        })
    }

    // Returns `true` if the provided [`LazyRawValue`] is a struct whose first annotation is
    // `$ion_symbol_table`.
    fn maybe_symbol_table(
        lazy_value: D::Value,
    ) -> IonResult<Result<LZPSymbolTableUpdate<'data, D>, D::Value>> {
        match lazy_value.annotations().next() {
            Some(Ok(SYMREF_ION_SYMBOL_TABLE)) => {
                Self::process_symbol_table(lazy_value.read()?.expect_struct()?).map(Ok)
            }
            _ => Ok(Err(lazy_value)),
        }
    }

    // Traverses a symbol table, processing the `symbols` and `imports` fields as needed to
    // populate the `PendingLst`.
    fn process_symbol_table<'top>(
        symbol_table: D::Struct,
    ) -> IonResult<LZPSymbolTableUpdate<'data, D>> {
        use crate::lazy::decoder::LazyRawField;
        use crate::lazy::decoder::LazyRawSequence;

        let mut symbols_field = None;
        let mut imports_field = None;
        for field in symbol_table.iter() {
            let field = field?;
            if field.name() == SYMREF_SYMBOLS {
                if symbols_field.replace(field.value()).is_some() {
                    return IonResult::decoding_error(
                        "found symbol table with multiple 'symbols' fields",
                    );
                }
            }
            if field.name() == SYMREF_IMPORTS {
                if imports_field.replace(field.value()).is_some() {
                    return IonResult::decoding_error(
                        "found symbol table with multiple 'imports' fields",
                    );
                }
            }
            // Ignore other fields
        }

        let (action, imports) = if let Some(imports) = imports_field {
            match imports.read()? {
                RawValueRef::Symbol(SYMREF_ION_SYMBOL_TABLE) => {
                    (LZPSymbolTableUpdateAction::Append, None)
                }
                RawValueRef::List(l) => (LZPSymbolTableUpdateAction::Reset, Some(l)),
                // Nulls and other types are ignored
                _ => (LZPSymbolTableUpdateAction::Reset, None),
            }
        } else {
            (LZPSymbolTableUpdateAction::Reset, None)
        };

        let symbols = match symbols_field {
            // Nulls and non-list values are ignored.
            Some(symbols) => symbols.read()?.maybe_list().ok(),
            None => None,
        };

        Ok(LZPSymbolTableUpdate {
            action,
            imports,
            symbols,
        })
    }
}

pub struct LazyProjSystemReader<'data, D: LazyDecoder<'data>> {
    lzpreader: LZPReader<'data, D>,
    symbol_table: Cell<LassoTable>,
    filter_spec: Step<String>,
    filter_spec_keys: BTreeSet<String>,
    step_symtab: BTreeMap<String, SymId>,
    filter: Option<Step<SymId>>,
}
pub type LazyProjBinarySystemReader<'data> = LazyProjSystemReader<'data, BinaryEncoding>;

#[derive(Debug)]
pub struct LazyStepValue<'top, 'data, D: LazyDecoder<'data>> {
    filter: &'top Step<SymId>,
    value: D::Value,
}

impl<'top, 'data, D: LazyDecoder<'data>> LazyStepValue<'top, 'data, D> {
    pub(crate) fn new(filter: &'top Step<SymId>, value: D::Value) -> Self {
        Self { filter, value }
    }
    pub(crate) fn extract(mut self) -> LazyStepValueIter<'top, 'data, D> {
        let filter = self.filter;
        let value = self.value;
        LazyStepValueIter { filter, value }
    }
}

#[derive(Debug)]
pub struct LazyStepValueIter<'top, 'data, D: LazyDecoder<'data>> {
    filter: &'top Step<SymId>,
    value: D::Value,
}

impl<'top, 'data, D: LazyDecoder<'data>> LazyStepValueIter<'top, 'data, D> {
    pub fn extract_all(mut self) -> IonResult<Vec<Vec<D::Value>>> {
        let mut result = vec![vec![], vec![]];
        self.filter.extract_into::<D>(self.value, &mut result)?;
        Ok(result)
    }
}

pub(crate) enum ValMatchCondition {
    Accept(PathId),
    Fail,
    Partial,
}

impl Step<SymId> {
    pub(crate) fn extract_into<'data, D: LazyDecoder<'data>>(
        &self,
        value: D::Value,
        result: &mut Vec<Vec<D::Value>>,
    ) -> IonResult<()> {
        for (mt, step) in &self.matches {
            match mt.matches(&value)? {
                ValMatchCondition::Accept(path_id) => {
                    result[path_id.0 - 1].push(value.clone());
                }
                ValMatchCondition::Fail => {
                    continue;
                }
                ValMatchCondition::Partial => {
                    step.extract_into(result)?;
                }
            }
        }

        Ok(())
    }
}

impl StepMatch<SymId> {
    #[inline]
    fn matches<'top, 'data, D: LazyDecoder<'data>>(
        &self,
        value: &'top D::Value,
    ) -> IonResult<ValMatchCondition> {
        let ttt = |b: IonResult<_>| {
            b.map(|b| {
                if b {
                    ValMatchCondition::Partial
                } else {
                    ValMatchCondition::Fail
                }
            })
        };
        match self {
            StepMatch::TopLevel(s) => {
                let inner = value.read()?;
                ttt(s.matches::<D>(&inner))
            }
            StepMatch::Seq(s) => {
                let inner = value.read()?;
                ttt(s.matches::<D>(&inner))
            }
            StepMatch::Struct(s) => {
                let inner = value.read()?;
                ttt(s.matches::<D>(&inner))
            }
            StepMatch::Accept(id) => Ok(ValMatchCondition::Accept(*id)),
            _ => Ok(ValMatchCondition::Fail),
        }
    }
}
impl AnnotMatch<SymId> {
    #[inline]
    fn matches_maybe<'top, 'data, D: LazyDecoder<'data>, A: LazyRawAnnotated<'data, D>>(
        maybe_annot: &Option<Self>,
        value: &'top A,
    ) -> IonResult<bool> {
        if let Some(annot) = maybe_annot {
            annot.matches::<D, A>(value)
        } else {
            Ok(value.annotations().next().is_none())
        }
    }

    #[inline]
    fn matches<'top, 'data, D: LazyDecoder<'data>, A: LazyRawAnnotated<'data, D>>(
        &self,
        value: &'top A,
    ) -> IonResult<bool> {
        value.annotations().are(
            self.annot
                .iter()
                .map(|symid| RawSymbolTokenRef::SymbolId(symid.get())),
        )
    }
}
impl TypeMatch {
    #[inline]
    fn matches_maybe<'top, T: LazyRawTyped>(
        maybe_typ: &Option<Self>,
        value: &'top T,
    ) -> IonResult<bool> {
        maybe_typ
            .map(|typ| typ.matches::<T>(value))
            .unwrap_or(Ok(true))
    }

    #[inline]
    fn matches<'top, T: LazyRawTyped>(&self, value: &'top T) -> IonResult<bool> {
        let val_type = value.ion_type();
        Ok(match (self, val_type) {
            (TypeMatch::Struct, IonType::Struct) => true,
            (TypeMatch::Seq, IonType::List | IonType::SExp) => true,
            _ => false,
        })
    }
}
impl SeqValMatch {
    #[inline]
    fn matches<'top, 'data, D: LazyDecoder<'data>>(
        &self,
        value: &'top D::Sequence,
    ) -> IonResult<bool> {
        Ok(match self {
            SeqValMatch::Any => true,
            SeqValMatch::Index { .. } => todo!("SeqValMatch::Index"),
        })
    }
}

impl SeqMatch<SymId> {
    fn matches<'top, 'data, D: LazyDecoder<'data>>(
        &self,
        value: &'top D::Value,
    ) -> IonResult<bool> {
        Ok(self.value.matches::<D>(value)?
            && AnnotMatch::matches_maybe::<D, _>(&self.annot, value)?
            && TypeMatch::matches_maybe::<_>(&self.typ, value)?)
    }
}
impl StructValMatch<SymId> {
    #[inline]
    fn matches<'top, 'data, D: LazyDecoder<'data>>(
        &self,
        value: &'top D::Struct,
    ) -> IonResult<bool> {
        Ok(match self {
            StructValMatch::Any => true,
            StructValMatch::Field { .. } => todo!("SeqValMatch::Field"),
        })
    }
}

impl StructMatch<SymId> {
    fn matches<'top, 'data, D: LazyDecoder<'data>>(
        &self,
        value: &'top D::Value,
    ) -> IonResult<bool> {
        Ok(AnnotMatch::matches_maybe::<D, _>(&self.annot, value)?
            && TypeMatch::matches_maybe::<_>(&self.typ, value)?
            && self.value.matches::<D>(value)?)
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for LazyStepValueIter<'top, 'data, D> {
    type Item = IonResult<(PathId, D::Value)>;

    fn next(&mut self) -> Option<Self::Item> {
        let ion_type = self.value.ion_type();
        let filtered: IonResult<Vec<_>> = self
            .filter
            .matches
            .iter()
            .filter_map(|(mat, step)| {
                //
                match mat.matches::<D>(&self.value) {
                    Ok(ValMatchCondition::Accept(id)) => Some(Ok((id, &self.value))),
                    Ok(ValMatchCondition::Fail) => None,
                    Ok(ValMatchCondition::Partial) => {
                        todo!()
                    }
                    Err(e) => Some(Err(e)),
                }
            })
            .collect();

        dbg!(&filtered);

        todo!()
    }
}

impl<'data> LazyProjBinarySystemReader<'data> {
    pub(crate) fn new(
        ion_data: &'data [u8],
        filter_spec: Step<String>,
    ) -> LazyProjBinarySystemReader<'data> {
        let lzpreader = LZPBinaryReader::new(ion_data);
        let symbol_table = Default::default();
        let filter_spec_keys: BTreeSet<String> = filter_spec.keys().into_iter().cloned().collect();
        let step_symtab = BTreeMap::new();
        let filter = None;

        LazyProjBinarySystemReader {
            lzpreader,
            symbol_table,
            filter_spec,
            filter_spec_keys,
            step_symtab,
            filter,
        }
    }
}

impl<'data, D: LazyDecoder<'data>> LazyProjSystemReader<'data, D> {
    pub fn next<'top>(&'top mut self) -> IonResult<Option<LazyStepValue<'top, 'data, D>>> {
        //-> IonResult<Option<LazyValue<'top, 'data, D, SymbolArena<'data>>>> {

        'next_value: loop {
            match self.lzpreader.next()? {
                LZPStreamItem::VersionMarker(_, _) => {
                    continue 'next_value;
                }
                LZPStreamItem::Value(value) => {
                    if let Some(filter) = &mut self.filter {
                        return Ok(Some(LazyStepValue::new(filter, value)));
                    } else {
                        return Ok(None);
                    }
                }
                LZPStreamItem::SymbolTableUpdate(update) => {
                    self.process_symbol_table(&update)?;
                    continue 'next_value;
                }
                LZPStreamItem::EndOfStream => return Ok(None),
            }
        }
    }

    fn process_symbol_table(&mut self, update: &LZPSymbolTableUpdate<'data, D>) -> IonResult<()> {
        let needed_keys: Option<BTreeSet<&str>> =
            if update.action == LZPSymbolTableUpdateAction::Reset {
                self.symbol_table.replace(LassoTable::default());
                self.step_symtab.clear();
                Some(self.filter_spec_keys.iter().map(|s| s.as_str()).collect())
            } else {
                if self.step_symtab.len() < self.filter_spec_keys.len() {
                    let mut needed_keys: BTreeSet<&str> =
                        self.filter_spec_keys.iter().map(|s| s.as_str()).collect();
                    for (k, _) in &self.step_symtab {
                        needed_keys.remove(k.as_str());
                    }
                    Some(needed_keys)
                } else {
                    None
                }
            };

        if let Some(_) = update.imports {
            return IonResult::decoding_error(
                "This implementation does not yet support shared symbol table imports",
            );
        }

        let symtab = self.symbol_table.get_mut();
        if let Some(mut needed_keys) = needed_keys {
            if let Some(syms) = &update.symbols {
                for sym in syms.iter() {
                    let symtxt: StrRef = sym?.read()?.expect_string()?;
                    let symtxt = symtxt.text();
                    let id = symtab.intern(symtxt);
                    if needed_keys.remove(symtxt) {
                        self.step_symtab.insert(symtxt.to_string(), id);
                    }
                }
            }
        } else {
            todo!("symtab with 'unneeded' keys");
        }

        self.rekey_filter()
    }

    fn rekey_filter(&mut self) -> IonResult<()> {
        dbg!(&self.step_symtab);
        dbg!(&self.filter_spec_keys);
        assert_eq!(self.step_symtab.len(), self.filter_spec_keys.len());

        dbg!(&self.filter);
        self.filter = Some(self.filter_spec.compile(&self.step_symtab));
        dbg!(&self.filter);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::constants::v1_0::system_symbol_ids;
    use crate::constants::v1_0::system_symbol_ids::ION_SYMBOL_TABLE;
    use crate::element::element_stream_reader::ElementStreamReader;
    use crate::element::element_stream_writer::ElementStreamWriter;
    use crate::ion_path_extractor::lazyproj::{
        AnnotMatch, LZPStreamItem, LazyProjBinarySystemReader, PathId, SeqAction, SeqMatch,
        SeqValMatch, Step, StepMatch, StructAction, StructMatch, StructValMatch, SymbolArena,
        TypeMatch,
    };
    //use crate::ion_path_extractor::proj2;
    use crate::ion_path_extractor::ui::Builder;
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
    use crate::lazy::binary::raw::value::LazyRawBinaryValue;
    use crate::lazy::encoding::BinaryEncoding;
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::symbol_table::SymbolLookup;
    use crate::{
        BinaryWriterBuilder, ElementReader, ElementWriter, IonResult, IonType, IonWriter,
        RawSymbolTokenRef, ReaderBuilder, Symbol, SymbolId, SymbolRefTable, SymbolTable,
    };
    use bytes::Buf;
    use nom::Slice;
    use std::collections::{HashMap, HashSet};
    use std::hint::black_box;
    use std::num::NonZeroUsize;
    use std::ops::Range;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[track_caller]
    fn assert_paths(searchPaths: &[&str], ionText: &str, expected: &[&str]) {
        //let mut builder = Builder::new();
        //for s in searchPaths {
        //    builder = builder.add_path(s).expect("add_path");
        //}
        //let res = builder.build();
        //assert!(res.is_ok());
    }

    #[track_caller]
    fn assert_path(searchPath: &str, ionText: &str, expected: &[&str]) {
        assert_paths(&[searchPath], ionText, expected)
    }

    #[test]
    fn mixed_path_components() {
        assert_path(
            "(foo * bar)",
            "{ foo: [ {bar: 1} ], foo: { baz: {bar: 2} } }",
            &["1", "2"],
        );
    }

    #[track_caller]
    fn to_binary_ion(text: &str) -> Vec<u8> {
        dbg!(&text);
        let mut out = vec![];
        let mut reader = ReaderBuilder::new().build(text).expect("reader");
        let elts = reader.read_all_elements().expect("read");
        let mut writer = BinaryWriterBuilder::new().build(&mut out).expect("f");
        writer.write_elements(elts.iter()).expect("write");
        writer.flush().expect("writer flush");
        out
    }

    #[test]
    fn testsxx() {
        let A = AnnotMatch {
            annot: vec!["A".to_string()],
        };
        let foo = StructValMatch::Field {
            name: "foo".to_string(),
        };
        let bar = StructValMatch::Field {
            name: "bar".to_string(),
        };
        // _.foo[*].A::bar
        let pm1: [StepMatch<String>; 5] = [
            StepMatch::TopLevel(SeqMatch::any_of_type(TypeMatch::Struct)),
            StructMatch::new(None, Some(TypeMatch::Seq), foo.clone()).into(),
            SeqMatch::any_of_type(TypeMatch::Struct).into(),
            StructMatch::new(Some(A.clone()), None, bar.clone()).into(),
            StepMatch::Accept(PathId(1)),
        ];
        // _.foo.*.A::bar
        let pm2 = [
            StepMatch::TopLevel(SeqMatch::any_of_type(TypeMatch::Struct)),
            StructMatch::new(None, Some(TypeMatch::Struct), foo.clone()).into(),
            StructMatch::any_of_type(TypeMatch::Struct).into(),
            StructMatch::new(Some(A.clone()), None, bar.clone()).into(),
            StepMatch::Accept(PathId(2)),
        ];

        //dbg!(&pm1);
        //dbg!(&pm2);

        let mut filter_array = Step::default();
        filter_array.add_path(&pm1);
        dbg!(filter_array.keys());

        let mut filter_struct = Step::default();
        filter_struct.add_path(&pm2);
        dbg!(filter_struct.keys());

        let mut filter_both = Step::default();
        filter_both.add_path(&pm1);
        filter_both.add_path(&pm2);
        dbg!(filter_both.keys());

        //dbg!(filter_both);

        let top_lvl_value = "{ foo: [ {bar: A::1} ], foo: { baz: {bar: A::2} } }";
        let stream: String = std::iter::repeat(top_lvl_value).take(5).collect();
        let data = to_binary_ion(stream.as_str());
        let mut preader = LazyProjBinarySystemReader::new(&data, filter_array);

        while let Some(mut next) = preader.next().expect("value") {
            dbg!(&next);
            let extracts = next.extract().extract_all();
            dbg!(&extracts);
        }
        dbg!("done");
    }

    #[test]
    fn test_st() {
        fn data() -> Vec<String> {
            let strs = ["foo", "bar", "baz"];
            let nums: Vec<_> = (1..=50).collect();
            let mut data = vec![];
            for n in nums {
                for s in strs {
                    data.push(format!("{}{}", s, n));
                }
            }

            data
        }
        let strs = data();

        let mut ids = [vec![], vec![], vec![]];

        let mut symtab = SymbolTable::default();
        for d in &strs {
            ids[0].push(symtab.intern(black_box(d)));
        }

        let mut symarena = SymbolArena::new();
        let mut id = NonZeroUsize::new(1).unwrap();
        for d in &strs {
            (symarena, id) = symarena.intern(black_box(d).as_str());
            ids[1].push(id.into());
        }

        let mut symarena2 = SymbolRefTable::new();
        for d in &strs {
            ids[2].push(symarena2.intern(black_box(d).as_str()).into());
        }

        for i in 0..ids[0].len() {
            assert_eq!(ids[0][i], ids[1][i]);
            assert_eq!(ids[0][i], ids[2][i]);
        }

        for d in &strs {
            //dbg!(d);
            let exemplar = symtab.sid_for(d);
            if symarena.sid_for(d).is_none() {
                symarena.dump();
            }
            assert_eq!(exemplar, symarena.sid_for(d));
            assert_eq!(exemplar, symarena2.sid_for(d));
        }

        for id in 1..strs.len() {
            let exemplar = symtab.text_for(id);
            assert_eq!(exemplar, symarena.text_for(id));
            assert_eq!(exemplar, symarena2.text_for(id));
        }
    }

    #[test]
    fn tests() {
        //////////////////////////////////////////
        /*

        Test case spec:

        single search path:
        {
          searchPath: <search path as ion>,
          data: <ion data to be read>,
          expected: <list containing expected matched values in order>
        }

        multiple search paths:
        {
          searchPaths: <list or s-exp with search paths as ion>,
          data: <same as single search path>,
          expected: <same as single search path>
        }

        Only difference is that for multiple the searchPath key is pluralized to searchPaths and expects an Ion sequence of
        search paths
        */

        // zero search paths ---------------------------------------------------------------------
        // no-op extractor, data doesn't matter
        assert_paths(&[], "{foo: 1}", &[]);
        assert_paths(&[], "(3 4)", &[]);
        assert_paths(&[], "99", &[]);
        assert_paths(&[], "[1, 2]", &[]);

        // Field only ----------------------------------------------------------------------------

        // matches
        assert_path("(foo)", "{foo: 1}", &["1"]);
        assert_path("[foo]", "{foo: 1}", &["1"]);
        assert_path("(foo bar)", "{foo: {bar : 2}}", &["2"]);

        enum Next {
            Annot(String),
            Field(String),
            Ordinal(usize),
            In(Level),
            None,
            Accept,
        }

        enum Level {
            Struct,
            Seq,
        }

        // escaped wildcard
        assert_path("('$ion_extractor_field'::*)", "{'*': 1, foo: 2}", &["1"]);

        // matches one sibling
        assert_path("(foo baz)", "{foo: {bar : 2, baz: 3}}", &["3"]);

        // multiple matches
        assert_path("(foo bar)", "{foo: {bar : 2, bar: 3}}", &["2", "3"]);

        // no match
        assert_path("(foo)", "{baz: 10}", &[]);
        assert_path("(foo baz)", "{foo: {bar : 2}}", &[]);

        // stepOut
        // assert_path("(foo bar)", "{foo: {bar : 2, bar: 3}}", &[2] );
        // assert_path("(foo bar baz)",  "{ foo: { bar: {baz: 1}, bar: {baz: 2} } }",  &[1] );

        // empty containers
        assert_path("(foo)", "{}", &[]);
        assert_path("(foo)", "()", &[]);
        assert_path("(foo)", "[]", &[]);

        // not containers
        assert_path("(foo)", "null", &[]);
        assert_path("(foo)", "true", &[]);
        assert_path("(foo)", "1", &[]);
        assert_path("(foo)", "1e0", &[]);
        assert_path("(foo)", "1.0", &[]);
        assert_path("(foo)", "2018T", &[]);
        assert_path("(foo)", "\"\"", &[]);
        assert_path("(foo)", "''", &[]);
        assert_path("(foo)", "{{ }}", &[]);
        assert_path("(foo)", "{{ \"\" }}", &[]);

        // Ordinal only --------------------------------------------------------------------------

        // matches
        assert_path("(0)", "[1]", &["1"]);
        assert_path("[0]", "[1]", &["1"]);
        assert_path("(0)", "(1)", &["1"]);
        assert_path("(0)", "{f: 1}", &["1"]);
        assert_path("(1)", "[1, 2]", &["2"]);
        assert_path("(1)", "(1 3)", &["3"]);
        assert_path("(1)", "{f1: 1, f2: 2}", &["2"]);
        assert_path("(0)", "[1, 2]", &["1"]);
        assert_path("(0)", "(1 3)", &["1"]);
        assert_path("(0)", "{f1: 1, f2: 2}", &["1"]);

        // out of bounds
        assert_path("(1)", "[1]", &[]);
        assert_path("(1)", "(1)", &[]);
        assert_path("(1)", "{foo: 1}", &[]);

        // empty containers
        assert_path("(0)", "[]", &[]);
        assert_path("(0)", "()", &[]);
        assert_path("(0)", "{}", &[]);

        // not containers
        assert_path("(0)", "null", &[]);
        assert_path("(0)", "true", &[]);
        assert_path("(0)", "1", &[]);
        assert_path("(0)", "1e0", &[]);
        assert_path("(0)", "1.0", &[]);
        assert_path("(0)", "2018T", &[]);
        assert_path("(0)", "\"\"", &[]);
        assert_path("(0)", "''", &[]);
        assert_path("(0)", "{{ }}", &[]);
        assert_path("(0)", "{{ \"\" }}", &[]);

        // Wildcard only -------------------------------------------------------------------------

        // matches
        assert_path("(*)", "[1]", &["1"]);
        assert_path("['*']", "[1]", &["1"]);
        assert_path("(*)", "(1)", &["1"]);
        assert_path("(*)", "{f: 1}", &["1"]);
        assert_path("(*)", "[1, 2]", &["1", "2"]);
        assert_path("(*)", "(1 3)", &["1", "3"]);
        assert_path("(*)", "{f1: 1, f2: 2}", &["1", "2"]);
        assert_path("(* *)", "[1, [2]]", &["2"]);
        assert_path("(* *)", "(1 (3))", &["3"]);
        assert_path("(* *)", "{f1: 1, f2: {f3: 2}}", &["2"]);

        // escape annotation is only valid as the first annotation
        assert_path(
            "(foo::'$ion_extractor_field'::*)",
            "[foo::'$ion_extractor_field'::1, foo::'$ion_extractor_field'::2]",
            &[
                "foo::'$ion_extractor_field'::1",
                "foo::'$ion_extractor_field'::2",
            ],
        );

        // insufficient depth
        assert_path("(* *)", "[1]", &[]);
        assert_path("(* *)", "(1)", &[]);
        assert_path("(* *)", "{f1: 1}", &[]);
        assert_path("(* *)", "[1, 2]", &[]);
        assert_path("(* *)", "(1 2)", &[]);
        assert_path("(* *)", "{f1: 1, f2: 2}", &[]);

        // step out
        //assert_path("(* *)", "[[1], [2]]", &[1], stepOutN: 2 ); -- no step out

        // empty containers
        assert_path("(*)", "[]", &[]);
        assert_path("(*)", "()", &[]);
        assert_path("(*)", "{}", &[]);

        // not containers
        assert_path("(*)", "null", &[]);
        assert_path("(*)", "true", &[]);
        assert_path("(*)", "1", &[]);
        assert_path("(*)", "1e0", &[]);
        assert_path("(*)", "1.0", &[]);
        assert_path("(*)", "2018T", &[]);
        assert_path("(*)", "\"\"", &[]);
        assert_path("(*)", "''", &[]);
        assert_path("(*)", "{{ }}", &[]);
        assert_path("(*)", "{{ \"\" }}", &[]);

        // Empty search path ---------------------------------------------------------------------

        // containers
        assert_path("()", "[1]", &["[1]"]);
        assert_path("[]", "[1]", &["[1]"]);
        assert_path("()", "(1)", &["(1)"]);
        assert_path("()", "{foo: 1}", &["{foo: 1}"]);

        // empty containers
        assert_path("()", "[]", &["[]"]);
        assert_path("()", "()", &["()"]);
        assert_path("()", "{}", &["{}"]);

        // not containers
        assert_path("()", "null", &["null"]);
        assert_path("()", "true", &["true"]);
        assert_path("()", "1", &["1"]);
        assert_path("()", "1e0", &["1e0"]);
        assert_path("()", "1.0", &["1.0"]);
        assert_path("()", "2018T", &["2018T"]);
        assert_path("()", "\"\"", &["\"\""]);
        assert_path("()", "''", &["''"]);
        assert_path("()", "{{ }}", &["{{ }}"]);
        assert_path("()", "{{ \"\" }}", &["{{ \"\" }}"]);

        // Mixed path components -----------------------------------------------------------------
        assert_path(
            "(foo 1)",
            "{ foo: [0, 1], foo: (0 2), foo: {a: 1, b: 3}, foo: 1, bar: [0, 1] }",
            &["1", "2", "3"],
        );
        assert_path(
            "[foo, '*']",
            "{ foo: [1], foo: (2), foo: {bar: 3}, foo: 1, bar: (9) }",
            &["1", "2", "3"],
        );
        assert_path(
            "(foo * bar)",
            "{ foo: [ {bar: 1} ], foo: { baz: {bar: 2} } }",
            &["1", "2"],
        );
        assert_path(
            "(foo * 0)",
            "{ foo: [1, [2]], foo: {bar: (3)} }",
            &["2", "3"],
        );
        assert_path("(foo bar 2)", "{abc: def, foo: {bar:[1, 2, 3]}}", &["3"]);
        assert_path(
            "(foo bar *)",
            "{abc: def, foo: {bar:[1, 2, 3]}}",
            &["1", "2", "3"],
        );
        assert_path(
            "(foo bar * baz)",
            "{abc: def, foo: {bar:[{baz:1}, {zar:2}, {baz:3}]}}",
            &["1", "3"],
        );

        // stepOut
        //{ searchPath: (foo * 0),
        //  "{
        //    foo: { first: [1], second: [2] },
        //    foo: { first: [10], second: [20] }
        //  }",
        //  &[1,10],}

        // Multiple search paths -----------------------------------------------------------------
        // all match
        assert_paths(&["(0)", "(foo)"], "{bar: 1, foo: 2}", &["1", "2"]);

        // none match
        assert_paths(&["(1)", "[foo]"], "[0]", &[]);

        // multiple matchers match the same value
        assert_paths(&["(1)", "(*)"], "[1, 2, 3]", &["1", "2", "2", "3"]);

        assert_paths(&["(foo 1)", "(foo 2)"], "{foo: [0, 1, 2]}", &["1", "2"]);

        // With annotations ----------------------------------------------------------------------
        assert_path("A::()", "A::1", &["A::1"]);
        assert_path("A::()", "1", &[]);
        assert_path(
            "A::(foo)",
            "$datagram::[
    A::{bar: 1},
    A::{foo: 2},
    {foo: 3}
  ]",
            &["2"],
        );

        assert_path("(A::'*')", "[A::1, 2]", &["A::1"]);
        assert_path(
            "('$ion_extractor_field'::*)",
            "{'*': A::1, foo: 2}",
            &["A::1"],
        );
        assert_path("(A::B::C::*)", "[A::B::C::1, B::A::C::2]", &["A::B::C::1"]);
        assert_path(
            "(foo A::2 bar)",
            "{ foo: [0, 1, A::{bar: 1}], foo: [0, 1, {bar: 2}] }",
            &["1"],
        );
        //////////////////////////////////////////
    }
}
