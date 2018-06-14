/// Types that support slicing by ranges.
pub trait BitSliceable<Range> {
    /// The type of the slice produced.
    type Slice;

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
    fn bit_slice(self, range: Range) -> Self::Slice;
}

