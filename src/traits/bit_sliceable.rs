use {BitRange, Bits};

/// Types that support slicing by ranges.
pub trait BitSliceable {
    /// The type of the slice produced.
    type Slice: Bits;

    /// Slices or re-slices the given object.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::{BitSlice, BitSliceable};
    ///
    /// let array = [0b01010011u16];
    /// let slice = BitSlice::from_slice(&array);
    ///
    /// assert_eq!( slice.bit_slice(1..3), slice.bit_slice(4..6) );
    /// assert_eq!( slice.bit_slice(1..3), slice.bit_slice(6..8) );
    ///
    /// assert_ne!( slice.bit_slice(2..4), slice.bit_slice(6..8) );
    /// assert_eq!( slice.bit_slice(2..4), slice.bit_slice(7..9) );
    /// ```
    fn bit_slice<R: BitRange>(self, range: R) -> Self::Slice;
}

impl<'a> BitSliceable for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice<R: BitRange>(self, range: R) -> &'a [bool] {
        let (start, count) = range.interpret_range(self.len() as u64)
            .expect("<&[bool]>::bit_slice");
        &self[start as usize .. (start + count) as usize]
    }
}

impl<'a> BitSliceable for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice<R: BitRange>(self, range: R) -> &'a mut [bool] {
        let (start, count) = range.interpret_range(self.len() as u64)
            .expect("<&mut [bool]>::bit_slice");
        &mut self[start as usize .. (start + count) as usize]
    }
}
