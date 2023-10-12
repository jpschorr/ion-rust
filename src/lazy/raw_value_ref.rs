use crate::lazy::decoder::LazyDecoder;
use crate::lazy::str_ref::StrRef;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonError, IonResult, IonType, RawSymbolTokenRef, Timestamp};
use std::fmt::{Debug, Formatter};

/// As RawValueRef represents a reference to an unresolved value read from the data stream.
/// If the value is a symbol, it only contains the information found in the data stream (a symbol ID
/// or text literal). If it is a symbol ID, a symbol table will be needed to find its associated text.
///
/// For a resolved version of this type, see [crate::lazy::value_ref::ValueRef].
pub enum RawValueRef<'data, D: LazyDecoder<'data>> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(StrRef<'data>),
    Symbol(RawSymbolTokenRef<'data>),
    Blob(&'data [u8]),
    Clob(&'data [u8]),
    SExp(D::Sequence),
    List(D::Sequence),
    Struct(D::Struct),
}

// Provides equality for scalar types, but not containers.
impl<'data, D: LazyDecoder<'data>> PartialEq for RawValueRef<'data, D> {
    fn eq(&self, other: &Self) -> bool {
        use RawValueRef::*;
        match (self, other) {
            (Null(i1), Null(i2)) => i1 == i2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Int(i1), Int(i2)) => i1 == i2,
            (Float(f1), Float(f2)) => f1 == f2,
            (Decimal(d1), Decimal(d2)) => d1 == d2,
            (Timestamp(t1), Timestamp(t2)) => t1 == t2,
            (String(s1), String(s2)) => s1 == s2,
            (Symbol(s1), Symbol(s2)) => s1 == s2,
            (Blob(b1), Blob(b2)) => b1 == b2,
            (Clob(c1), Clob(c2)) => c1 == c2,
            // We cannot compare lazy containers as we cannot guarantee that their complete contents
            // are available in the buffer. Is `{foo: bar}` equal to `{foo: b`?
            _ => false,
        }
    }
}

impl<'data, D: LazyDecoder<'data>> Debug for RawValueRef<'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RawValueRef::Null(ion_type) => write!(f, "null.{}", ion_type),
            RawValueRef::Bool(b) => write!(f, "{}", b),
            RawValueRef::Int(i) => write!(f, "{}", i),
            RawValueRef::Float(float) => write!(f, "{}", float),
            RawValueRef::Decimal(d) => write!(f, "{}", d),
            RawValueRef::Timestamp(t) => write!(f, "{}", t),
            RawValueRef::String(s) => write!(f, "{}", s),
            RawValueRef::Symbol(s) => write!(f, "{:?}", s),
            RawValueRef::Blob(b) => write!(f, "blob ({} bytes)", b.len()),
            RawValueRef::Clob(c) => write!(f, "clob ({} bytes)", c.len()),
            RawValueRef::SExp(s) => write!(f, "sexp={:?}", s),
            RawValueRef::List(l) => write!(f, "{:?}", l),
            RawValueRef::Struct(s) => write!(f, "{:?}", s),
        }
    }
}

impl<'data, D: LazyDecoder<'data>> RawValueRef<'data, D> {
    pub fn maybe_null(self) -> Option<IonType> {
        if let RawValueRef::Null(ion_type) = self {
            Some(ion_type)
        } else {
            None
        }
    }

    pub fn expect_null(self) -> IonResult<IonType> {
        self.maybe_null()
            .ok_or_else(|| IonError::decoding_error("expected a null"))
    }

    pub fn maybe_bool(self) -> Result<bool, Self> {
        match self {
            RawValueRef::Bool(b) => Ok(b),
            _ => Err(self),
        }
    }
    pub fn expect_bool(self) -> IonResult<bool> {
        self.maybe_bool()
            .map_err(|_| IonError::decoding_error("expected a bool"))
    }

    pub fn maybe_int(self) -> Result<Int, Self> {
        match self {
            RawValueRef::Int(i) => Ok(i),
            _ => Err(self),
        }
    }
    pub fn expect_int(self) -> IonResult<Int> {
        self.maybe_int()
            .map_err(|_| IonError::decoding_error("expected a int"))
    }

    pub fn maybe_i64(self) -> Result<i64, Self> {
        match self {
            RawValueRef::Int(ref i) => i.as_i64().ok_or_else(|| self),
            _ => Err(self),
        }
    }
    pub fn expect_i64(self) -> IonResult<i64> {
        self.maybe_i64().map_err(|val| {
            IonError::decoding_error(format!("expected an i64 (int), found: {:?}", val))
        })
    }

    pub fn maybe_float(self) -> Result<f64, Self> {
        match self {
            RawValueRef::Float(f) => Ok(f),
            _ => Err(self),
        }
    }
    pub fn expect_float(self) -> IonResult<f64> {
        self.maybe_float()
            .map_err(|_| IonError::decoding_error("expected a float"))
    }

    pub fn maybe_decimal(self) -> Result<Decimal, Self> {
        match self {
            RawValueRef::Decimal(d) => Ok(d),
            _ => Err(self),
        }
    }
    pub fn expect_decimal(self) -> IonResult<Decimal> {
        self.maybe_decimal()
            .map_err(|_| IonError::decoding_error("expected a decimal"))
    }

    pub fn maybe_timestamp(self) -> Result<Timestamp, Self> {
        match self {
            RawValueRef::Timestamp(t) => Ok(t),
            _ => Err(self),
        }
    }
    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        self.maybe_timestamp()
            .map_err(|_| IonError::decoding_error("expected a timestamp"))
    }

    pub fn maybe_string(self) -> Result<StrRef<'data>, Self> {
        match self {
            RawValueRef::String(s) => Ok(s),
            _ => Err(self),
        }
    }
    pub fn expect_string(self) -> IonResult<StrRef<'data>> {
        self.maybe_string()
            .map_err(|_| IonError::decoding_error("expected a string"))
    }

    pub fn maybe_symbol(self) -> Result<RawSymbolTokenRef<'data>, Self> {
        match self {
            RawValueRef::Symbol(s) => Ok(s),
            _ => Err(self),
        }
    }
    pub fn expect_symbol(self) -> IonResult<RawSymbolTokenRef<'data>> {
        self.maybe_symbol()
            .map_err(|_| IonError::decoding_error("expected a symbol"))
    }

    pub fn maybe_blob(self) -> Result<&'data [u8], Self> {
        match self {
            RawValueRef::Blob(d) => Ok(d),
            _ => Err(self),
        }
    }
    pub fn expect_blob(self) -> IonResult<&'data [u8]> {
        self.maybe_blob()
            .map_err(|_| IonError::decoding_error("expected a blob"))
    }

    pub fn maybe_clob(self) -> Result<&'data [u8], Self> {
        match self {
            RawValueRef::Clob(d) => Ok(d),
            _ => Err(self),
        }
    }
    pub fn expect_clob(self) -> IonResult<&'data [u8]> {
        self.maybe_clob()
            .map_err(|_| IonError::decoding_error("expected a clob"))
    }

    pub fn maybe_list(self) -> Result<D::Sequence, Self> {
        match self {
            RawValueRef::List(seq) => Ok(seq),
            _ => Err(self),
        }
    }
    pub fn expect_list(self) -> IonResult<D::Sequence> {
        self.maybe_list()
            .map_err(|_| IonError::decoding_error("expected a list"))
    }

    pub fn maybe_sexp(self) -> Result<D::Sequence, Self> {
        match self {
            RawValueRef::SExp(seq) => Ok(seq),
            _ => Err(self),
        }
    }
    pub fn expect_sexp(self) -> IonResult<D::Sequence> {
        self.maybe_sexp()
            .map_err(|_| IonError::decoding_error("expected a sexp"))
    }

    pub fn maybe_struct(self) -> Result<D::Struct, Self> {
        match self {
            RawValueRef::Struct(strct) => Ok(strct),
            _ => Err(self),
        }
    }
    pub fn expect_struct(self) -> IonResult<D::Struct> {
        self.maybe_struct()
            .map_err(|val| IonError::decoding_error(format!("expected a struct, found: {:?}", val)))
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::reader::LazyRawBinaryReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::{Decimal, IonResult, IonType, RawSymbolTokenRef, Timestamp};

    #[test]
    fn expect_type() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            null
            true
            1
            2.5e0
            2.5
            2023-04-29T13:45:38.281Z
            foo
            "hello"
            {{Blob}}
            {{"Clob"}}
            [this, is, a, list]
            (this is a sexp)
            {this: is, a: struct}
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(&ion_data);
        // IVM
        reader.next()?.expect_ivm()?;
        // Symbol table
        reader.next()?.expect_value()?.read()?.expect_struct()?;
        // User data
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );
        assert!(reader.next()?.expect_value()?.read()?.expect_bool()?);
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            1.into()
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_float()?,
            2.5f64
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_decimal()?,
            Decimal::new(25, -1)
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_timestamp()?,
            Timestamp::with_ymd(2023, 4, 29)
                .with_hms(13, 45, 38)
                .with_milliseconds(281)
                .with_offset(0)
                .build()?
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            RawSymbolTokenRef::SymbolId(10) // foo
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_string()?,
            "hello"
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_blob()?,
            &[0x06, 0x5A, 0x1B] // Base64-decoded "Blob"
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_clob()?,
            "Clob".as_bytes()
        );
        assert!(reader.next()?.expect_value()?.read()?.expect_list().is_ok());
        assert!(reader.next()?.expect_value()?.read()?.expect_sexp().is_ok());
        assert!(reader
            .next()?
            .expect_value()?
            .read()?
            .expect_struct()
            .is_ok());

        Ok(())
    }

    #[test]
    fn expect_type_error() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            true
            null.bool
        "#,
        )?;
        let mut reader = LazyRawBinaryReader::new(&ion_data);
        // IVM
        reader.next()?.expect_ivm()?;

        let bool_value = reader.next()?.expect_value()?;
        assert!(bool_value.read()?.expect_null().is_err());
        assert!(bool_value.read()?.expect_int().is_err());
        assert!(bool_value.read()?.expect_float().is_err());
        assert!(bool_value.read()?.expect_decimal().is_err());
        assert!(bool_value.read()?.expect_timestamp().is_err());
        assert!(bool_value.read()?.expect_symbol().is_err());
        assert!(bool_value.read()?.expect_string().is_err());
        assert!(bool_value.read()?.expect_blob().is_err());
        assert!(bool_value.read()?.expect_clob().is_err());
        assert!(bool_value.read()?.expect_list().is_err());
        assert!(bool_value.read()?.expect_sexp().is_err());
        assert!(bool_value.read()?.expect_struct().is_err());

        let null_value = reader.next()?.expect_value()?;
        assert!(null_value.read()?.expect_bool().is_err());
        Ok(())
    }
}
