use std::cmp::{max, Ordering};
use std::hash::{Hash, Hasher};
use std::ops::{self, Range, RangeFrom, RangeTo, RangeFull};

use super::storage::*;
use super::slice::*;
use super::traits::*;

/// A bit-vector.
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
    pub fn new() -> Self {
        Self::with_block_capacity(1)
    }

    /// Creates a new, empty bit-vector with the given bit capacity.
    pub fn with_capacity(nbits: u64) -> Self {
        Self::with_block_capacity(Block::ceil_div_nbits(nbits))
    }

    /// Creates a new, empty bit-vector with the given block capacity.
    pub fn with_block_capacity(nblocks: usize) -> Self {
        BV {
            bits: Vec::with_capacity(nblocks).into_boxed_slice(),
            len: 0,
        }
    }

    /// The number of bits in the bit-vector.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// The number of blocks used by this bit-vector.
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
        self.bits = copy_resize(&self.bits, new_cap);
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

    /// Adjusts the capacity to at least `additional` blocks beyond those used.
    pub fn block_reserve_exact(&mut self, additional: usize) {
        let new_cap = self.block_len() + additional;
        self.bits = copy_resize(&self.bits, new_cap);
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
        self.reserve(1);
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
        let padding = Block::nbits() - Block::last_block_bits(self.len);
        if padding == 0 { return; }

        let last = self.bits.len() - 1;
        let mask = Block::low_mask(padding);
        if value {
            self.bits[last] = self.bits[last] | mask;
        } else {
            self.bits[last] = self.bits[last] & !mask;
        }

        self.len += padding as u64;
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

    fn slice(self, range: Range<u64>) -> BitSlice<'a, Block> {
        self.as_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn slice(self, range: Range<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn slice(self, range: RangeFrom<u64>) -> BitSlice<'a, Block> {
        self.as_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn slice(self, range: RangeFrom<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn slice(self, range: RangeTo<u64>) -> BitSlice<'a, Block> {
        self.as_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn slice(self, range: RangeTo<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a BV<Block> {
    type Slice = BitSlice<'a, Block>;

    fn slice(self, _: RangeFull) -> BitSlice<'a, Block> {
        self.as_slice()
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a mut BV<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn slice(self, _: RangeFull) -> BitSliceMut<'a, Block> {
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

impl<Block: BlockType> Hash for BV<Block> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}
