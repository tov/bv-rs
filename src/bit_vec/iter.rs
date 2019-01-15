use BitVec;
use BlockType;
use Bits;

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
#[derive(Clone)]
pub struct BitVecIter<'a, Block: 'a> {
    bv: &'a BitVec<Block>,
    index: u64,
}

impl<'a, Block> From<&'a BitVec<Block>> for BitVecIter<'a, Block> {
    fn from(bv: &'a BitVec<Block>) -> Self {
        Self {bv, index: 0}
    }
}

impl<'a, Block: BlockType> Iterator for BitVecIter<'a, Block> {
    type Item = bool;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.index < self.bv.len() {
            let result = self.bv.get_bit(self.index);
            self.index += 1;
            Some(result)
        } else {
            None
        }
    }
}
