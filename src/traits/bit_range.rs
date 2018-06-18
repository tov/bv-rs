#[cfg(inclusive_range)]
use util;

use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

// Types that can be used as ranges for slicing bit vectors.
//
// This abstracts over the various range types such as `Range`, `RangeFrom`,
// etc.
pub trait BitRange {
    // Calculates the start bit and count for a given bit range and vector length.
    //
    // # Arguments
    //
    // - `self` – the range
    //
    // - `len` - the length of the vector to slice
    //
    // - `who` - the entity to report in the error, if there's a problem
    //
    // # Results
    //
    // `Ok((start, count))` for success, or `Err(msg)` if the range is bad or out
    // of bounds.
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String>;
}

impl BitRange for Range<u64> {
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String> {
        if self.start <= self.end {
            if self.end <= len {
                Ok((self.start, self.end - self.start))
            } else {
                Err(format!("{}: range out of bounds", who))
            }
        } else {
            Err(format!("{}: bad range", who))
        }
    }
}

impl BitRange for RangeTo<u64> {
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String> {
        if self.end <= len {
            Ok((0, self.end))
        } else {
            Err(format!("{}: range out of bounds", who))
        }
    }
}

impl BitRange for RangeFrom<u64> {
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String> {
        if self.start <= len {
            Ok((self.start, len - self.start))
        } else {
            Err(format!("{}: range out of bounds", who))
        }
    }
}

impl BitRange for RangeFull {
    fn interpret_range(&self, len: u64, _who: &str) -> Result<(u64, u64), String> {
        Ok((0, len))
    }
}

#[cfg(inclusive_range)]
impl BitRange for RangeInclusive<u64> {
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String> {
        match util::get_inclusive_bounds(self) {
            Some((start, end)) => {
                if end < len {
                    Ok((start, end - start + 1))
                } else {
                    Err(format!("{}: range out of bounds", who))
                }
            }

            _ => Err(format!("{}: bad range", who))
        }
    }
}

#[cfg(inclusive_range)]
impl BitRange for RangeToInclusive<u64> {
    fn interpret_range(&self, len: u64, who: &str) -> Result<(u64, u64), String> {
        if self.end < len {
            Ok((0, self.end + 1))
        } else {
            Err(format!("{}: range out of bounds", who))
        }
    }
}

#[cfg(test)]
mod test {
    use super::BitRange;
    
    #[test]
    fn interpret_ranges() {
        assert_eq!( (0 .. 2).interpret_range(10, "me"), Ok((0, 2)));
        assert_eq!( (3 .. 7).interpret_range(10, "me"), Ok((3, 4)));
        assert_eq!( (3 .. 10).interpret_range(10, "me"), Ok((3, 7)));
        assert!( (3 .. 11).interpret_range(10, "me").is_err() );

        assert_eq!( (.. 2).interpret_range(10, "me"), Ok((0, 2)));
        assert_eq!( (.. 7).interpret_range(10, "me"), Ok((0, 7)));
        assert_eq!( (.. 10).interpret_range(10, "me"), Ok((0, 10)));
        assert!( (.. 11).interpret_range(10, "me").is_err() );

        assert_eq!( (0 ..).interpret_range(10, "me"), Ok((0, 10)));
        assert_eq!( (7 ..).interpret_range(10, "me"), Ok((7, 3)));
        assert_eq!( (9 ..).interpret_range(10, "me"), Ok((9, 1)));
        assert_eq!( (10 ..).interpret_range(10, "me"), Ok((10, 0)));
        assert!( (11 ..).interpret_range(10, "me").is_err() );

        assert_eq!( (..).interpret_range(10, "me"), Ok((0, 10)) );
    }

    #[test]
    #[cfg(inclusive_range)]
    fn interpret_inclusive_ranges() {
        use std::ops::RangeToInclusive;
        let rti = |bound| RangeToInclusive { end: bound };

        assert_eq!( rti(2).interpret_range(10, "me"), Ok((0, 3)));
        assert_eq!( rti(7).interpret_range(10, "me"), Ok((0, 8)));
        assert_eq!( rti(9).interpret_range(10, "me"), Ok((0, 10)));
        assert!( rti(10).interpret_range(10, "me").is_err() );
        assert!( rti(11).interpret_range(10, "me").is_err() );
    }
}
