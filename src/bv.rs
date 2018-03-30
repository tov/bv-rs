use std::cmp::{max, Ordering};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{self, Range, RangeFrom, RangeTo, RangeFull};

use super::storage::*;
use super::slice::*;
use super::traits::*;

/// A bit-vector, akin to `Vec<bool>` but packed.
#[derive(Clone)]
pub struct BV<Block = usize> {
    bits:   Box<[Block]>,
    len:    u64,
}

fn copy_resize<Block: BlockType>(slice: &[Block], len: usize) -> Box<[Block]> {
    let mut result = Vec::with_capacity(len);

    for i in 0 .. len {
        if i < slice.len() {
            result.push(slice[i]);
        } else {
            result.push(Block::zero());
        }
    }

    result.into_boxed_slice()
}

impl<Block: BlockType> BV<Block> {
    /// Creates a new, empty bit-vector of one block.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::{BV, BitVec};
    ///
    /// let mut bv: BV = BV::new();
    /// assert_eq!(bv.len(), 0);
    ///
    /// bv.push(true);
    /// bv.push(false);
    /// bv.push(true);
    /// assert_eq!(bv.len(), 3);
    ///
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.get_bit(2), true);
    /// ```
    pub fn new() -> Self {
        Self::with_block_capacity(1)
    }

    /// Creates a new, empty bit-vector with the given bit capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BV;
    ///
    /// let mut bv: BV<u16> = BV::with_capacity(20);
    /// assert_eq!(bv.capacity(), 32);
    /// ```
    pub fn with_capacity(nbits: u64) -> Self {
        Self::with_block_capacity(Block::ceil_div_nbits(nbits))
    }

    /// Creates a new, empty bit-vector with the given block capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BV;
    ///
    /// let mut bv: BV<u16> = BV::with_block_capacity(8);
    /// assert_eq!(bv.capacity(), 128);
    /// ```
    pub fn with_block_capacity(nblocks: usize) -> Self {
        let mut result = Self::from_block(Block::zero(), nblocks);
        result.len = 0;
        result
    }

    /// Creates a new bit-vector of size `len`, filled with all 0s or 1s
    /// depending on `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BV<u64> = BV::new_fill(false, 100);
    ///
    /// assert_eq!( bv.get_bit(0), false );
    /// assert_eq!( bv.len(), 100 );
    /// ```
    pub fn new_fill(value: bool, len: u64) -> Self {
        let mut result = Self::new_block_fill(value, Block::ceil_div_nbits(len));
        result.len = len;
        result
    }

    /// Creates a new bit-vector filled with `value`, made up of `nblocks` blocks.
    #[inline]
    fn new_block_fill(value: bool, nblocks: usize) -> Self {
        let block = if value {!Block::zero()} else {Block::zero()};
        Self::from_block(block, nblocks)
    }

    #[inline]
    fn from_block(init: Block, nblocks: usize) -> Self {
        BV {
            bits: vec![ init; nblocks ].into_boxed_slice(),
            len:  Block::mul_nbits(nblocks),
        }
    }

    /// The number of bits in the bit-vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BV;
    ///
    /// let mut bv: BV = BV::new();
    /// assert_eq!(bv.len(), 0);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 1);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 2);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 3);
    /// ```
    pub fn len(&self) -> u64 {
        self.len
    }

    /// The number of blocks used by this bit-vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BV<u64> = BV::new_fill(false, 100);
    ///
    /// assert_eq!( bv.len(), 100 );
    /// assert_eq!( bv.block_len(), 2 );
    /// ```
    pub fn block_len(&self) -> usize {
        Block::ceil_div_nbits(self.len())
    }

    /// The capacity of the bit-vector in bits.
    pub fn capacity(&self) -> u64 {
        Block::mul_nbits(self.block_capacity())
    }

    /// The capacity of the bit-vector in blocks.
    pub fn block_capacity(&self) -> usize {
        self.bits.len()
    }

    /// Adjust the capacity to hold at least `additional` additional bits.
    ///
    /// May reserve more to avoid frequent reallocations.
    pub fn reserve(&mut self, additional: u64) {
        let old_cap = self.capacity();
        self.reserve_exact(max(1, max(additional, old_cap)));
    }

    /// Adjust the capacity to hold at least `additional` additional blocks.
    ///
    /// May reserve more to avoid frequent reallocations.
    pub fn block_reserve(&mut self, additional: usize) {
        let old_cap = self.block_capacity();
        self.block_reserve_exact(max(1, max(additional, old_cap)));
    }

    /// Adjust the capacity to hold at least `additional` additional bits.
    pub fn reserve_exact(&mut self, additional: u64) {
        let new_cap = Block::ceil_div_nbits(self.len() + additional);
        if new_cap > self.block_capacity() {
            self.bits = copy_resize(&self.bits, new_cap);
        }
    }

    /// Adjusts the capacity to at least `additional` blocks beyond those used.
    pub fn block_reserve_exact(&mut self, additional: usize) {
        let new_cap = self.block_len() + additional;
        if new_cap > self.block_capacity() {
            self.bits = copy_resize(&self.bits, new_cap);
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    pub fn shrink_to_fit(&mut self) {
        if self.block_capacity() > self.block_len() {
            self.bits = copy_resize(&self.bits, self.block_len());
        }
    }

    /// Converts the vector into `Box<[Block]>`.
    ///
    /// Note that this will *not* drop any excess capacity.
    pub fn into_boxed_slice(self) -> Box<[Block]> {
        self.bits
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// Note that this method has no effect on the capacity of the bit-vector.
    pub fn truncate(&mut self, len: u64) {
        if len < self.len {
            self.len = len;
        }
    }

    /// Resizes the bit-vector, filling with `value` if it has to grow.
    pub fn resize(&mut self, len: u64, value: bool) {
        match len.cmp(&self.len) {
            Ordering::Less => {
                self.len = len
            },
            Ordering::Equal => { },
            Ordering::Greater => {
                {
                    let growth = len - self.len();
                    self.reserve(growth);
                }

                self.align_block(value);

                let block = if value {!Block::zero()} else {Block::zero()};
                while self.len < len {
                    self.push_block(block);
                }

                self.len = len;
            },
        }
    }

    /// Gets a slice to a `BV`.
    pub fn as_slice(&self) -> BitSlice<Block> {
        unsafe {
            BitSlice::from_raw_parts(self.bits.as_ptr(), 0, self.len)
        }
    }

    /// Gets a mutable slice to a `BV`.
    pub fn as_mut_slice(&mut self) -> BitSliceMut<Block> {
        unsafe {
            BitSliceMut::from_raw_parts(self.bits.as_mut_ptr(), 0, self.len)
        }
    }

    /// Adds the given `bool` to the end of the bit-vector.
    pub fn push(&mut self, value: bool) {
        if self.len() == self.capacity() - 1 {
            self.reserve(1);
        }

        let old_len = self.len;
        self.len = old_len + 1;
        self.set_bit(old_len, value);
    }

    /// Removes and returnst the last element of the bit-vector, or `None` if empty.
    pub fn pop(&mut self) -> Option<bool> {
        if self.len > 0 {
            let new_len = self.len - 1;
            let result = self.get_bit(new_len);
            self.len = new_len;
            Some(result)
        } else {
            None
        }
    }

    /// Removes all elements from the bit-vector.
    ///
    /// Does not change the capacity.
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Does the bit-vector have no elements?
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<Block: BlockType> BitVec for BV<Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len()
    }

    fn bit_offset(&self) -> u8 {
        0
    }

    fn get_block(&self, position: usize) -> Block {
        self.bits[position]
    }
}

impl<Block: BlockType> BitVecMut for BV<Block> {
    fn set_block(&mut self, position: usize, value: Block) {
        self.bits[position] = value;
    }
}

impl<Block: BlockType> BitVecPush for BV<Block> {
    fn push_bit(&mut self, value: bool) {
        self.push(value);
    }

    fn pop_bit(&mut self) -> Option<bool> {
        self.pop()
    }

    fn align_block(&mut self, value: bool) {
        let keep_bits = Block::mod_nbits(self.len);
        if keep_bits > 0 {
            let last_index = self.block_len() - 1;
            let last = &mut self.bits[last_index];
            if value {
                *last = *last | !Block::low_mask(keep_bits);
            } else {
                *last = *last & Block::low_mask(keep_bits);
            }
            self.len += (Block::nbits() - keep_bits) as u64;
        }
    }

    fn push_block(&mut self, value: Block) {
        self.align_block(false);
        self.block_reserve(1);
        self.len += Block::nbits() as u64;
        let last = self.block_len() - 1;
        self.set_block(last, value);
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> BitSlice<'a, Block> {
        self.as_slice()
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> BitSliceMut<'a, Block> {
        self.as_mut_slice()
    }
}

impl<Block: BlockType> ops::Index<u64> for BV<Block> {
    type Output = bool;

    fn index(&self, index: u64) -> &bool {
        if self.get_bit(index) {&true} else {&false}
    }
}

impl<Block: BlockType> PartialEq for BV<Block> {
    fn eq(&self, other: &BV<Block>) -> bool {
        self.as_slice().eq(&other.as_slice())
    }
}

impl<Block: BlockType> PartialOrd for BV<Block> {
    fn partial_cmp(&self, other: &BV<Block>) -> Option<Ordering> {
        self.as_slice().partial_cmp(&other.as_slice())
    }
}

impl<Block: BlockType> Eq for BV<Block> {}

impl<Block: BlockType> Ord for BV<Block> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_slice().cmp(&other.as_slice())
    }
}

impl<Block: BlockType + Hash> Hash for BV<Block> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<Block: BlockType> fmt::Debug for BV<Block> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bit_slicing() {
        let v: BV<u8> = bv![ false, true, true, false, true, false, false, true,
                             true, false, false, true, false, true, true, false ];
        assert!( !v.get_bit(0) );
        assert!(  v.get_bit(1) );
        assert!(  v.get_bit(2) );
        assert!( !v.get_bit(3) );

        let w = v.bit_slice(2..14);
        assert_eq!( w.bit_len(), 12 );
        assert_eq!( w.bit_offset(), 2 );

        assert!(  w.get_bit(0) );
        assert!( !w.get_bit(1) );

        assert_eq!( w.get_bits(2, 4), 0b00001001 );
        assert_eq!( w.get_bits(2, 5), 0b00011001 );
        assert_eq!( w.get_bits(2, 8), 0b10011001 );
        assert_eq!( w.get_bits(3, 8), 0b01001100 );

        assert_eq!( w.get_block(0), 0b10010110 );
        assert_eq!( w.get_block(1), 0b01101001 );
    }

    #[test]
    fn resize() {
        let mut v: BV<u8> = bv![ true; 13 ];
        assert_eq!( v.len(), 13 );

        v.resize(50, false);
        assert_eq!( v.len(), 50 );
        assert_eq!( v.get_bit(12), true );
        assert_eq!( v.get_bit(13), false );
        assert_eq!( v.get_bit(49), false );

        v.resize(67, true);
        assert_eq!( v.len(), 67 );
        assert_eq!( v.get_bit(12), true );
        assert_eq!( v.get_bit(13), false );
        assert_eq!( v.get_bit(49), false );
        assert_eq!( v.get_bit(50), true );
        assert_eq!( v.get_bit(66), true );

        v.set_bit(3, false);
        assert_eq!( v.get_bit(3), false );

        v.resize(17, false);
        assert_eq!( v.len(), 17 );
        assert_eq!( v.get_bit(1), true );
        assert_eq!( v.get_bit(2), true );
        assert_eq!( v.get_bit(3), false );
        assert_eq!( v.get_bit(4), true );
        assert_eq!( v.get_bit(16), false );
    }

    #[test]
    fn shrink_to_fit() {
        let mut v: BV<u8> = BV::with_capacity(100);
        assert_eq!( v.capacity(), 104 );

        v.push(true);
        v.push(false);
        assert_eq!( v.len(), 2 );
        assert_eq!( v.capacity(), 104 );

        v.shrink_to_fit();
        assert_eq!( v.len(), 2 );
        assert_eq!( v.capacity(), 8 );
    }

    #[test]
    fn into_boxed_slice() {
        let v: BV<u8> = bv![ true, false, true ];
        assert_eq!( v.capacity(), 8 );
        let bs = v.into_boxed_slice();
        assert_eq!( bs.len(), 1 );
        assert_eq!( bs[0], 0b00000101 );
    }

    #[test]
    fn truncate() {
        let mut v: BV<u8> = BV::new_fill(true, 80);
        assert_eq!( v.len(), 80 );
        assert_eq!( v.get_bit(34), true );

        v.truncate(45);
        assert_eq!( v.len(), 45 );
        assert_eq!( v.get_bit(34), true );
    }

    #[test]
    fn as_mut_slice() {
        let mut v: BV<u8> = BV::new_fill(true, 77);
        let w = v.as_mut_slice();
        assert_eq!( w.len(), 77 );
        assert_eq!( w.get_block(0), 0b11111111 );
    }

    #[test]
    fn pop() {
        let mut v: BV<u8> = bv![true, false, true];
        assert_eq!( v.pop(), Some(true) );
        assert_eq!( v.pop(), Some(false) );
        assert_eq!( v.pop(), Some(true) );
        assert_eq!( v.pop(), None );
    }

    #[test]
    fn clear_and_is_empty() {
        let mut v: BV<u8> = bv![true, false, true];
        assert_eq!( v.len(), 3 );
        assert!( !v.is_empty() );
        v.clear();
        assert_eq!( v.len(), 0 );
        assert!( v.is_empty() );
    }

    #[test]
    fn push_bit_and_pop_bit() {
        let mut v: BV<u8> = BV::new();
        v.push_bit(true);
        v.push_bit(false);
        assert_eq!( v.pop_bit(), Some(false) );
        assert_eq!( v.pop_bit(), Some(true) );
        assert_eq!( v.pop_bit(), None );
    }
}
