use Bits;
use std::cmp::Ordering;

/// An iterator over a `BitVec`.
///
/// # Examples
///
/// ```
/// use bv::*;
///
/// let bv: BitVec<usize> = bit_vec![ true, false ];
/// let mut iter = bv.iter();
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), Some(false));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct BitsIter<T> {
    bits: T,
    pos: u64,
}
// Invariant: pos <= bits.block_len()

impl<T: Bits> BitsIter<T> {
    /// Creates a new block iterator from a `Bits` instance.
    pub fn new(bits: T) -> Self {
        BitsIter { bits, pos:  0, }
    }

    /// Returns the number of *bits* remaining in the iterator.
    pub fn bit_len(&self) -> u64 {
        self.bits.bit_len() - self.pos
    }
}

impl<T: Bits> From<T> for BitsIter<T> {
    fn from(bits: T) -> Self {
        Self::new(bits)
    }
}

impl<T: Bits> Iterator for BitsIter<T> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.pos < self.bits.bit_len() {
            let result = Some(self.bits.get_bit(self.pos));
            self.pos += 1;
            result
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<T: Bits> ExactSizeIterator for BitsIter<T> {
    fn len(&self) -> usize {
        (self.bits.bit_len() - self.pos) as usize
    }
}

fn cmp_bits_iter<T, U>(iter1: &BitsIter<T>, iter2: &BitsIter<U>) -> Ordering
    where T: Bits,
          U: Bits<Block = T::Block> {

    let len1 = iter1.bit_len();
    let len2 = iter2.bit_len();
    let len_cmp = len1.cmp(&len2);
    if len_cmp != Ordering::Equal { return len_cmp; }

    for i in 0 .. iter1.len() as u64 {
        let block1 = iter1.bits.get_bit(iter1.pos + i);
        let block2 = iter2.bits.get_bit(iter2.pos + i);
        let block_cmp = block1.cmp(&block2);
        if block_cmp != Ordering::Equal { return block_cmp; }
    }

    return Ordering::Equal;
}

impl<T, U> PartialEq<BitsIter<U>> for BitsIter<T>
    where T: Bits,
          U: Bits<Block = T::Block> {

    fn eq(&self, other: &BitsIter<U>) -> bool {
        cmp_bits_iter(self, other) == Ordering::Equal
    }
}

impl<T: Bits> Eq for BitsIter<T> {}

impl<T, U> PartialOrd<BitsIter<U>> for BitsIter<T>
    where T: Bits,
          U: Bits<Block = T::Block> {

    fn partial_cmp(&self, other: &BitsIter<U>) -> Option<Ordering> {
        Some(cmp_bits_iter(self, other))
    }
}

impl<T: Bits> Ord for BitsIter<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_bits_iter(self, other)
    }
}

#[cfg(test)]
mod test {
    use BitVec;
    use super::*;

    fn eq_iter<T, U>(bits1: T, bits2: U) -> bool
        where T: Bits,
              U: Bits<Block = T::Block> {

        let i1 = BitsIter::new(bits1);
        let i2 = BitsIter::new(bits2);
        i1 == i2
    }

    #[test]
    fn empty() {
        let bv1: BitVec = bit_vec![];
        let bv2: BitVec = bit_vec![];
        assert!( eq_iter(&bv1, &bv2) );
    }

    #[test]
    fn same() {
        let bv1: BitVec = bit_vec![true, false, true];
        let bv2: BitVec = bit_vec![true, false, true];
        assert!( eq_iter(&bv1, &bv2) );
    }

    #[test]
    fn different() {
        let bv1: BitVec = bit_vec![true, false, false];
        let bv2: BitVec = bit_vec![true, false, true];
        assert!( !eq_iter(&bv1, &bv2) );
    }

    #[test]
    fn different_lengths() {
        let bv1: BitVec = bit_vec![true, false, true, false];
        let bv2: BitVec = bit_vec![true, false, true];
        assert!( !eq_iter(&bv1, &bv2) );
    }
}
