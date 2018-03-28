use std::marker::PhantomData;
use std::{ops,ptr};

use super::traits::{BitVec, BitVecMut};
use super::storage::BlockType;

/// A slice of a bit-vector. Akin to `&'a [bool]` but packed.
#[derive(Copy, Clone)]
pub struct BitSlice<'a, Block> {
    bits:   *const Block,
    offset: u8,
    len:    u64,
    marker: PhantomData<&'a ()>,
}

/// A mutable slice of a bit-vector. Akin to `&'a mut [bool]` but packed.
pub struct BitSliceMut<'a, Block> {
    bits:   *mut Block,
    offset: u8,
    len:    u64,
    marker: PhantomData<&'a mut ()>,
}

impl<'a, Block: BlockType> BitSlice<'a, Block> {
    /// Creates a `BitSlice` from a pointer to its data, an offset where the bits start, and the
    /// number of available bits. This is unsafe because the size of the passed-in buffer is not
    /// checked. It must hold at least `offset + len` bits or the resulting behavior is undefined.
    pub unsafe fn from_raw_parts(bits: *const Block, offset: u8, len: u64) -> Self {
        BitSlice {
            bits,
            offset,
            len,
            marker: PhantomData
        }
    }
}

impl<'a, Block: BlockType> BitSliceMut<'a, Block> {
    /// Creates a `BitSliceMut` from a pointer to its data, an offset where the bits start, and
    /// the number of available bits. This is unsafe because the size of the passed-in buffer is
    /// not checked. It must hold at least `offset + len` bits or the resulting behavior is
    /// undefined.
    pub unsafe fn from_raw_parts(bits: *mut Block, offset: u8, len: u64) -> Self {
        BitSliceMut {
            bits,
            offset,
            len,
            marker: PhantomData
        }
    }

    pub fn as_immut(&self) -> BitSlice<Block> {
        BitSlice {
            bits:   self.bits,
            offset: self.offset,
            len:    self.len,
            marker: PhantomData,
        }
    }
}

impl<'a, Block: BlockType> BitVec for BitSlice<'a, Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn bit_offset(&self) -> u8 {
        self.offset
    }

    fn get_block(&self, position: usize) -> <Self as BitVec>::Block {
        assert!(position < self.block_len(), "BitSlice::get_block: out of bounds");

        unsafe {
            ptr::read(self.bits.offset(position as isize))
        }
    }
}

impl<'a, Block: BlockType> BitVec for BitSliceMut<'a, Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn bit_offset(&self) -> u8 {
        self.offset
    }

    fn get_block(&self, position: usize) -> Block {
        assert!(position < self.block_len(), "BitSliceMut::get_block: out of bounds");

        unsafe {
            ptr::read(self.bits.offset(position as isize))
        }
    }
}

impl<'a, Block: BlockType> BitVecMut for BitSliceMut<'a, Block> {
    fn set_block(&mut self, position: usize, value: Block) {
        assert!(position < self.block_len(), "BitSliceMut::set_block: out of bounds");

        unsafe {
            ptr::write(self.bits.offset(position as isize), value)
        }
    }
}

impl<'a, Block: BlockType> ops::Index<u64> for BitSlice<'a, Block> {
    type Output = bool;

    fn index(&self, index: u64) -> &bool {
        if self.get_bit(index) {&true} else {&false}
    }
}

impl<'a, Block: BlockType> ops::Index<u64> for BitSliceMut<'a, Block> {
    type Output = bool;

    fn index(&self, index: u64) -> &bool {
        if self.get_bit(index) {&true} else {&false}
    }
}

/// Types that support (re-)slicing by ranges.
pub trait Sliceable<Range> {
    /// (Re-)slices the given object.
    fn slice(self, range: Range) -> Self;
}

impl<'a, Block: BlockType> Sliceable<ops::Range<u64>> for BitSlice<'a, Block> {
    fn slice(self, range: ops::Range<u64>) -> Self {
        assert!(range.start <= range.end, "BitSlice::slice: bad range");
        assert!(range.end <= self.len, "BitSlice::slice: out of bounds");

        let start_bits   = self.offset as u64 + range.start;
        let start_block  = Block::div_nbits(start_bits);
        let start_offset = Block::mod_nbits(start_bits) as u8;

        BitSlice {
            bits:   unsafe { self.bits.offset(start_block as isize) },
            offset: start_offset,
            len:    range.end - range.start,
            marker: PhantomData,
        }
    }
}

impl<'a, Block: BlockType> Sliceable<ops::Range<u64>> for BitSliceMut<'a, Block> {
    fn slice(self, range: ops::Range<u64>) -> Self {
        assert!(range.start <= range.end, "BitSliceMut::slice: bad range");
        assert!(range.end <= self.len, "BitSliceMut::slice: out of bounds");

        let start_bits   = self.offset as u64 + range.start;
        let start_block  = Block::div_nbits(start_bits);
        let start_offset = Block::mod_nbits(start_bits) as u8;

        BitSliceMut {
            bits:   unsafe { self.bits.offset(start_block as isize) },
            offset: start_offset,
            len:    range.end - range.start,
            marker: PhantomData,
        }
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeFrom<u64>> for BitSlice<'a, Block> {
    fn slice(self, range: ops::RangeFrom<u64>) -> Self {
        let len = self.len;
        self.slice(range.start .. len)
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeFrom<u64>> for BitSliceMut<'a, Block> {
    fn slice(self, range: ops::RangeFrom<u64>) -> Self {
        let len = self.len;
        self.slice(range.start .. len)
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeTo<u64>> for BitSlice<'a, Block> {
    fn slice(self, range: ops::RangeTo<u64>) -> Self {
        self.slice(0 .. range.end)
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeTo<u64>> for BitSliceMut<'a, Block> {
    fn slice(self, range: ops::RangeTo<u64>) -> Self {
        self.slice(0 .. range.end)
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeFull> for BitSlice<'a, Block> {
    fn slice(self, _: ops::RangeFull) -> Self {
        let len = self.len;
        self.slice(0 .. len)
    }
}

impl<'a, Block: BlockType> Sliceable<ops::RangeFull> for BitSliceMut<'a, Block> {
    fn slice(self, _: ops::RangeFull) -> Self {
        let len = self.len;
        self.slice(0 .. len)
    }
}

/// An iterator over the blocks of a bit slice.
pub struct BitSliceBlockIter<'a, Block>(BitSlice<'a, Block>);

impl<'a, Block: BlockType> Iterator for BitSliceBlockIter<'a, Block> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
        unimplemented!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.0.block_len();
        (len, Some(len))
    }
}
