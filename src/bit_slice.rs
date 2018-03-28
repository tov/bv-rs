use std::marker::PhantomData;

use super::storage::BlockType;

/// A slice of a bit-vector. Akin to `&'a [bool]` but packed.
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
}