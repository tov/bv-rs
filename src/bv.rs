use std::cmp::max;

use super::storage::*;
use super::slice::*;

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
}

