// Copyright Amazon.com, Inc. or its affiliates.

use crate::integration_testing::IVM;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::{
    LazyRawBinaryField, LazyRawBinaryStruct, RawBinaryStructIterator,
};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::sequence::{LazyRawBinarySequence, RawBinarySequenceIterator};
use crate::lazy::binary::raw::value::LazyRawBinaryValue;
use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawFieldPrivate};
use crate::lazy::decoder::{
    LazyDecoder, LazyRawField, LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue,
};
use crate::lazy::encoding::BinaryEncoding;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::reader::{LazyBinaryReader, LazyReader};
use crate::lazy::system_reader::LazySystemReader;
use crate::result::IonFailure;
use crate::{IonResult, IonType, RawSymbolTokenRef, SymbolId};

mod lazyproj;
mod ui;

// TODO
struct PathErr {}

/*
/// The Ion 1.0 binary encoding.
#[derive(Clone, Debug)]
pub struct ProjBinaryEncoding;

impl<'data> LazyDecoder<'data> for ProjBinaryEncoding {
    type Reader = LazyProjRawBinaryReader<'data>;
    type Value = LazyRawBinaryValue<'data>;
    type Sequence = LazyRawBinarySequence<'data>;
    type Struct = LazyRawBinaryStruct<'data>;
    type AnnotationsIterator = RawBinaryAnnotationsIterator<'data>;
}

impl<'data> LazyRawValue<'data, ProjBinaryEncoding> for LazyRawBinaryValue<'data> {
    fn ion_type(&self) -> IonType {
        self.ion_type()
    }

    fn is_null(&self) -> bool {
        self.is_null()
    }

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.annotations()
    }

    fn read(&self) -> IonResult<RawValueRef<'data, ProjBinaryEncoding>> {
        let value_ref = self.read()?;
        Ok(value_ref)
    }
}
impl<'data> LazyRawSequence<'data, ProjBinaryEncoding> for LazyRawBinarySequence<'data> {
    type Iterator = RawBinarySequenceIterator<'data>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawBinarySequence::iter(self)
    }

    fn as_value(&self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyContainerPrivate<'data, ProjBinaryEncoding> for LazyRawBinarySequence<'data> {
    fn from_value(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinarySequence { value }
    }
}
impl<'data> LazyContainerPrivate<'data, ProjBinaryEncoding> for LazyRawBinaryStruct<'data> {
    fn from_value(value: LazyRawBinaryValue<'data>) -> Self {
        LazyRawBinaryStruct { value }
    }
}

impl<'data> LazyRawStruct<'data, ProjBinaryEncoding> for LazyRawBinaryStruct<'data> {
    type Field = LazyRawBinaryField<'data>;
    type Iterator = RawBinaryStructIterator<'data>;

    fn annotations(&self) -> RawBinaryAnnotationsIterator<'data> {
        self.annotations()
    }

    fn find(&self, name: &str) -> IonResult<Option<LazyRawBinaryValue<'data>>> {
        self.find(name)
    }

    fn get(&self, name: &str) -> IonResult<Option<RawValueRef<'data, ProjBinaryEncoding>>> {
        self.get(name)
    }

    fn iter(&self) -> Self::Iterator {
        self.iter()
    }
}
impl<'data> LazyRawFieldPrivate<'data, ProjBinaryEncoding> for LazyRawBinaryField<'data> {
    fn into_value(self) -> LazyRawBinaryValue<'data> {
        self.value
    }
}

impl<'data> LazyRawField<'data, ProjBinaryEncoding> for LazyRawBinaryField<'data> {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        LazyRawBinaryField::name(self)
    }

    fn value(&self) -> LazyRawBinaryValue<'data> {
        self.value()
    }
}

pub struct LazyProjRawBinaryReader<'data> {
    raw_reader: LazyRawBinaryReader<'data>,
}
pub type LazyProjBinaryReader<'data> = LazyReader<'data, ProjBinaryEncoding>;
pub type LazyProjBinarySystemReader<'data> = LazySystemReader<'data, ProjBinaryEncoding>;

impl<'data> LazyProjRawBinaryReader<'data> {
    fn from_reader(raw_reader: LazyRawBinaryReader) -> LazyProjRawBinaryReader {
        Self { raw_reader }
    }
}

impl<'data> LazyRawReader<'data, ProjBinaryEncoding> for LazyProjRawBinaryReader<'data> {
    fn new(data: &'data [u8]) -> Self {
        LazyProjRawBinaryReader::new(data)
    }

    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, ProjBinaryEncoding>> {
        self.next()
    }
}

impl<'data> LazyProjBinaryReader<'data> {
    pub fn new(ion_data: &'data [u8]) -> IonResult<LazyProjBinaryReader<'data>> {
        if ion_data.len() < IVM.len() {
            return IonResult::decoding_error("input is too short to be recognized as Ion");
        } else if ion_data[..IVM.len()] != IVM {
            return IonResult::decoding_error("input does not begin with an Ion version marker");
        }

        let raw_reader = LazyRawBinaryReader::new(ion_data);
        let raw_reader = LazyProjRawBinaryReader::from_reader(raw_reader);
        let system_reader = LazySystemReader::from_reader(raw_reader);
        LazyReader::from_reader(system_reader)
    }
}

 */
/*
pub mod proj2 {
    use crate::constants::v1_0::system_symbol_ids::{IMPORTS, ION_SYMBOL_TABLE, SYMBOLS};
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
    use crate::lazy::decoder::private::LazyContainerPrivate;
    use crate::lazy::decoder::LazyRawReader;
    use crate::lazy::decoder::{LazyDecoder, LazyRawValue};
    use crate::lazy::encoding::BinaryEncoding;
    use crate::lazy::r#struct::LazyStruct;
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::lazy::reader::LazyReader;
    use crate::lazy::system_reader::LazySystemReader;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::lazy::value::LazyValue;
    use crate::symbol_table::SymbolLookup;
    use crate::{IonResult, IonType, RawSymbolTokenRef, Symbol, SymbolId, SymbolTable};

    // Symbol IDs used for processing symbol table structs
    const SYMREF_ION_SYMBOL_TABLE: RawSymbolTokenRef =
        RawSymbolTokenRef::SymbolId(ION_SYMBOL_TABLE);
    const SYMREF_IMPORTS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(IMPORTS);
    const SYMREF_SYMBOLS: RawSymbolTokenRef = RawSymbolTokenRef::SymbolId(SYMBOLS);

    pub struct LazyProjSystemReader<'data, D: LazyDecoder<'data>> {
        raw_reader: D::Reader,
        symbol_table: SymbolTable,
    }
    pub type LazyProjBinarySystemReader<'data> = LazyProjSystemReader<'data, BinaryEncoding>;

    impl<'data> LazyProjBinarySystemReader<'data> {
        pub(crate) fn new(ion_data: &'data [u8]) -> LazyProjBinarySystemReader<'data> {
            let raw_reader = LazyRawBinaryReader::new(ion_data);

            LazyProjBinarySystemReader {
                raw_reader,
                symbol_table: Default::default(),
            }
        }
    }

    pub fn create<'data>(ion_data: &'data [u8]) -> IonResult<LazyProjBinarySystemReader<'data>> {
        let sysreader = LazyProjBinarySystemReader::new(ion_data);
        Ok(sysreader)
    }

    impl<'data, D: LazyDecoder<'data>> SymbolLookup for LazyProjSystemReader<'data, D> {
        fn sid_for<A: AsRef<str>>(&self, text: &A) -> Option<SymbolId> {
            todo!()
        }

        fn symbol_for(&self, sid: SymbolId) -> Option<&Symbol> {
            todo!()
        }

        fn len(&self) -> usize {
            todo!()
        }
    }

    impl<'data, D: LazyDecoder<'data>> LazyProjSystemReader<'data, D> {
        // Returns `true` if the provided [`LazyRawValue`] is a struct whose first annotation is
        // `$ion_symbol_table`.
        fn is_symbol_table_struct(lazy_value: &D::Value) -> IonResult<bool> {
            if lazy_value.ion_type() != IonType::Struct {
                return Ok(false);
            }
            if let Some(symbol_ref) = lazy_value.annotations().next() {
                return Ok(symbol_ref? == SYMREF_ION_SYMBOL_TABLE);
            };
            Ok(false)
        }

        pub fn next_value<'top>(
            &'top mut self,
        ) -> IonResult<Option<LazyValue<'top, 'data, D, Self>>> {
            loop {
                //Self::apply_pending_lst(symbol_table, pending_lst);
                let lazy_raw_value = match self.raw_reader.next()? {
                    RawStreamItem::VersionMarker(_, _) => continue,
                    RawStreamItem::Value(lazy_raw_value) => lazy_raw_value,
                    RawStreamItem::EndOfStream => return Ok(None),
                };
                if Self::is_symbol_table_struct(&lazy_raw_value)? {
                    // process the symbol table, but do not surface it
                    self.process_symbol_table(&lazy_raw_value)?;
                } else {
                    return Ok(Some(LazyValue::new(&self, lazy_raw_value)));
                }
            }
        }

        // Traverses a symbol table, processing the `symbols` and `imports` fields as needed to
        // populate the `PendingLst`.
        fn process_symbol_table<'top>(&'top mut self, symbol_table: &D::Value) -> IonResult<()> {
            Ok(())
        }
    }
}

 */

mod sm {
    use crate::SymbolId;
    use std::collections::HashMap;

    enum CStep {
        Index(usize),
        WildCard(),
        Field(SymbolId),
    }

    type CAnnotations = Vec<SymbolId>;

    struct CNode {
        annot: CAnnotations,
        children: HashMap<CStep, CNode>,
        terminal: bool,
    }
}

#[cfg(test)]
mod tests {
    use crate::constants::v1_0::system_symbol_ids;
    use crate::constants::v1_0::system_symbol_ids::ION_SYMBOL_TABLE;
    use crate::element::element_stream_reader::ElementStreamReader;
    use crate::element::element_stream_writer::ElementStreamWriter;
    //use crate::ion_path_extractor::proj2;
    use crate::ion_path_extractor::ui::Builder;
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
    use crate::lazy::binary::raw::value::LazyRawBinaryValue;
    use crate::lazy::encoding::BinaryEncoding;
    use crate::lazy::raw_stream_item::RawStreamItem;
    use crate::{
        BinaryWriterBuilder, ElementReader, ElementWriter, IonResult, IonType, IonWriter,
        RawSymbolTokenRef, ReaderBuilder, SymbolId,
    };
    use std::collections::HashSet;
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

    /*
        #[test]
        fn testsxx() {
            type PathId = usize;
            enum Next {
                Any,
                None,
                Annot(SymbolId),
                Field(SymbolId),
                Ordinal(usize),
                In(Level),
                Accept(PathId),
            }

            enum Level {
                Struct,
                Seq,
                Any,
            }

            // "(foo * bar)"
            [
                Next::In(Level::Struct),
                Next::Field(10),
                Next::In(Level::Any),
                Next::Any,
                Next::In(Level::Struct),
                Next::Field(11),
                Next::Accept(1),
            ];
            // _.foo[*].bar
            // _.foo.*.bar
            enum State {
                Struct,
                Seq,
            }
            enum Action {
                Accept(usize),
                Reject,
                Continue,
            }
            struct AnnotationFind {
                annotations: Vec<SymbolId>,
            }
            struct StructFindAny {
                annot: AnnotationFind,
            }
            struct StructFind {
                annot: AnnotationFind,
                field: SymbolId,
            }
            struct SeqFindAny {
                annot: AnnotationFind,
            }
            struct SeqFind {
                annot: AnnotationFind,
                ordinal: usize,
            }

            enum StructNext {
                Annot(SymbolId),
                Field(SymbolId),
                In(Level),
                Accept(PathId),
            }

            enum Levelx {
                Struct,
                Seq,
                Any,
            }

            //
            let data = "{ foo: [ {bar: 1} ], foo: { baz: {bar: 2} } }";
            let mut out = vec![];
            let mut reader = ReaderBuilder::new().build(data).expect("reader");
            let elts = reader.read_all_elements().expect("read");
            dbg!(&elts);
            let mut writer = BinaryWriterBuilder::new().build(&mut out).expect("f");
            writer.write_elements(elts.iter()).expect("write");
            writer.flush();

            ///////
            let mut rrr = proj2::LazyProjSystemReader::new(&out);
            rrr.next_value().expect("foo");
            ///////

            let keys = HashSet::from(["foo", "bar"]);
            use crate::lazy::decoder::LazyDecoder;

            dbg!(&out);
            let mut read = LazyRawBinaryReader::new(&out);
            while let top_level = read.next().expect("f") {
                match top_level {
                    RawStreamItem::VersionMarker(_, _) => {}
                    RawStreamItem::Value(tpv) => {
                        let tpv: LazyRawBinaryValue = tpv;

                        if tpv.ion_type() == IonType::Struct
                            && tpv.annotations().next()
                                == Some(Ok(RawSymbolTokenRef::SymbolId(ION_SYMBOL_TABLE)))
                        {
                            dbg!("Symbol table");
                            let val = tpv.read().expect("sym t read");
                            let sts = val.expect_struct().expect("sym t struct");
                            for field in sts.iter() {
                                match field {
                                    Ok(field) => {
                                        //
                                        let name = field.name();
                                        let value = field.into_value();
                                        dbg!(&name, value.read());
                                        if name
                                            == RawSymbolTokenRef::SymbolId(system_symbol_ids::SYMBOLS)
                                        {
                                            let mut next_id = AtomicUsize::new(10);
                                            for x in value.read().unwrap().expect_list().unwrap().iter()
                                            {
                                                let key =
                                                    x.unwrap().read().unwrap().expect_string().unwrap();
                                                let key = key.text();
                                                if keys.contains(&key) {
                                                    dbg!(&key, next_id.fetch_add(1, Ordering::Relaxed));
                                                }
                                            }
                                        }
                                    }
                                    Err(_) => {
                                        todo!()
                                    }
                                }
                            }
                        } else {
                            dbg!(tpv.read());
                        }
                    }
                    RawStreamItem::EndOfStream => {
                        break;
                    }
                }
            }
        }
    */
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
