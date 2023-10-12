use crate::lazy::binary::immutable_buffer::ImmutableBuffer;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{IonResult, RawSymbolTokenRef};

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct RawBinaryAnnotationsIterator<'a> {
    buffer: ImmutableBuffer<'a>,
}

impl<'a> RawBinaryAnnotationsIterator<'a> {
    pub(crate) fn new(buffer: ImmutableBuffer<'a>) -> RawBinaryAnnotationsIterator<'a> {
        RawBinaryAnnotationsIterator { buffer }
    }
}

impl<'data> RawBinaryAnnotationsIterator<'data> {
    pub fn are<I: IntoIterator<Item = RawSymbolTokenRef<'data>>>(
        mut self,
        annotations_to_match: I,
    ) -> IonResult<bool> {
        for to_match in annotations_to_match {
            match self.next() {
                Some(Ok(actual)) if actual == to_match => {}
                Some(Err(e)) => return Err(e),
                Some(_) | None => return Ok(false),
            }
        }
        // We've exhausted `annotations_to_match`, now make sure `self` is empty
        Ok(self.next().is_none())
    }
}

impl<'a> Iterator for RawBinaryAnnotationsIterator<'a> {
    type Item = IonResult<RawSymbolTokenRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }
        // TODO: If the VarUInt doesn't end before the annotations sequence does (i.e. the stream is
        //       malformed, this will surface an `Incomplete` instead of a more descriptive error.
        let (var_uint, buffer_after_var_uint) = match self.buffer.read_var_uint() {
            Ok(output) => output,
            Err(error) => return Some(Err(error)),
        };
        let symbol_id = RawSymbolTokenRef::SymbolId(var_uint.value());
        self.buffer = buffer_after_var_uint;
        Some(Ok(symbol_id))
    }
}
