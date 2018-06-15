#[cfg(inclusive_range)]
use util;

use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

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

impl<'a> BitSliceable<RangeFull> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, _: RangeFull) -> &'a [bool] {
        self
    }
}

impl<'a> BitSliceable<RangeFull> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, _: RangeFull) -> &'a mut [bool] {
        self
    }
}

impl<'a> BitSliceable<Range<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: Range<u64>) -> &'a [bool] {
        &self[range.start as usize .. range.end as usize]
    }
}

impl<'a> BitSliceable<Range<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: Range<u64>) -> &'a mut [bool] {
        &mut self[range.start as usize .. range.end as usize]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeInclusive<u64>) -> &'a [bool] {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("<&[bool]>::bit_slice: bad inclusive range");
        // Adding 1 means we could overflow a 32-bit `usize` here, but
        // we can't construct a RangeInclusive on stable without using
        // the `..=` token, which breaks older rustcs.
        &self[start as usize .. end as usize + 1]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeInclusive<u64>) -> &'a mut [bool] {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("<&mut [bool]>::bit_slice: bad inclusive range");
        &mut self[start as usize .. end as usize + 1]
    }
}

impl<'a> BitSliceable<RangeFrom<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeFrom<u64>) -> &'a [bool] {
        &self[range.start as usize ..]
    }
}

impl<'a> BitSliceable<RangeFrom<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeFrom<u64>) -> &'a mut [bool] {
        &mut self[range.start as usize ..]
    }
}

impl<'a> BitSliceable<RangeTo<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeTo<u64>) -> &'a [bool] {
        &self[.. range.end as usize]
    }
}

impl<'a> BitSliceable<RangeTo<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeTo<u64>) -> &'a mut [bool] {
        &mut self[.. range.end as usize]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeToInclusive<u64>) -> &'a [bool] {
        &self[RangeToInclusive { end: range.end as usize }]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeToInclusive<u64>) -> &'a mut [bool] {
        &mut self[RangeToInclusive { end: range.end as usize }]
    }
}

