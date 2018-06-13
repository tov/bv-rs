#[cfg(inclusive_range)]
use std::ops::RangeInclusive;

#[cfg(inclusive_range)]
pub fn get_inclusive_bounds(range: &RangeInclusive<u64>) -> Option<(u64, u64)> {
    let mut r1 = range.clone();
    let mut r2 = range.clone();
    Some((r1.next()?, r2.next_back()?))
}

