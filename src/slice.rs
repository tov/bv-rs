use std::marker::PhantomData;
use std::{cmp, fmt, hash, ptr};
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

#[cfg(inclusive_range)]
use util;
use iter::BlockIter;
use traits::{Bits, BitsMut, BitSliceable};
use storage::{Address, BlockType};

/*
 * We represent bit-slices as raw pointers to `Block`s. The slice stores an
 * offset, which is the number of bits to skip at the beginning of the slice,
 * and a length, which is the total number of bits in the slice.
 *
 * INVARIANTS:
 *  - `offset < Block::nbits()`.
 *  - The buffer is large enough to store `offset + len` bits.
 */

/// A slice of a bit-vector; akin to `&'a [bool]` but packed.
///
/// # Examples
///
/// ```
/// use bv::*;
///
/// let array = [0b00110101u16];
/// let mut slice = array.bit_slice(..8);
/// assert_eq!( slice[0], true );
/// assert_eq!( slice[1], false );
///
/// slice = slice.bit_slice(1..8);
/// assert_eq!( slice[0], false );
/// assert_eq!( slice[1], true );
/// ```
#[derive(Copy, Clone)]
pub struct BitSlice<'a, Block> {
    bits:   *const Block,
    offset: u8,
    len:    u64,
    marker: PhantomData<&'a ()>,
}

/// A mutable slice of a bit-vector; akin to `&'a mut [bool]` but packed.
///
/// # Examples
///
/// ```
/// use bv::*;
///
/// let mut array = [0b00110101u16];
///
/// {
///     let mut slice = BitSliceMut::from_slice(&mut array);
///     assert_eq!( slice[0], true );
///     assert_eq!( slice[1], false );
///
///     slice.set_bit(0, false);
/// }
///
/// assert_eq!( array[0], 0b00110100u16 );
/// ```
pub struct BitSliceMut<'a, Block> {
    bits:   *mut Block,
    offset: u8,
    len:    u64,
    marker: PhantomData<&'a mut ()>,
}

impl<'a, Block: BlockType> BitSlice<'a, Block> {
    /// Creates a `BitSlice` from an array slice of blocks.
    ///
    /// The size is always a multiple of
    /// `Block::nbits()`. If you want a different size, slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::{BitSlice, BitSliceable};
    ///
    /// let v = vec![0b01010011u16, 0u16];
    /// let slice = BitSlice::from_slice(&v).bit_slice(..7);
    /// assert_eq!( slice.len(), 7 );
    /// assert_eq!( slice[0], true );
    /// assert_eq!( slice[1], true );
    /// assert_eq!( slice[2], false );
    /// ```
    pub fn from_slice(blocks: &'a [Block]) -> Self {
        BitSlice {
            bits:   blocks.as_ptr(),
            offset: 0,
            len:    Block::mul_nbits(blocks.len()),
            marker: PhantomData,
        }
    }

    /// Creates a `BitSlice` from a pointer to its data, an offset where the bits start, and the
    /// number of available bits.
    ///
    /// This is unsafe because the size of the passed-in buffer is not
    /// checked. It must hold at least `offset + len` bits or the resulting behavior is undefined.
    ///
    /// Method [`from_slice`](struct.BitSlice.html#method.from_slice),
    /// possibly followed by further slicing, is the preferred way to turn a slice or vector of
    /// blocks into a `BitSlice`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitSlice;
    ///
    /// let v = vec![0b01010011u16, 0u16];
    /// let slice = unsafe { BitSlice::from_raw_parts(v.as_ptr(), 0, 8) };
    /// assert_eq!( slice[0], true );
    /// assert_eq!( slice[1], true );
    /// assert_eq!( slice[2], false );
    /// ```
    pub unsafe fn from_raw_parts(bits: *const Block, offset: u8, len: u64) -> Self {
        BitSlice {
            bits,
            offset,
            len,
            marker: PhantomData,
        }
    }

    /// The number of bits in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec = bit_vec![ true, true, false, true ];
    /// let slice = bv.bit_slice(..3);
    ///
    /// assert_eq!( bv.len(), 4 );
    /// assert_eq!( slice.len(), 3 );
    /// ```
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns whether there are no bits in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec = bit_vec![ true, true, false, true ];
    /// let slice0 = bv.bit_slice(3..3);
    /// let slice1 = bv.bit_slice(3..4);
    ///
    /// assert!(  slice0.is_empty() );
    /// assert!( !slice1.is_empty() );
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, Block: BlockType> BitSliceMut<'a, Block> {
    /// Creates a `BitSliceMut` from a mutable array slice of blocks.
    ///
    /// The size is always a multiple of `Block::nbits()`. If you want a different size,
    /// slice.
    pub fn from_slice(blocks: &mut [Block]) -> Self {
        BitSliceMut {
            bits:   blocks.as_mut_ptr(),
            offset: 0,
            len:    Block::mul_nbits(blocks.len()),
            marker: PhantomData,
        }
    }

    /// Creates a `BitSliceMut` from a pointer to its data, an offset where the bits start, and
    /// the number of available bits.
    ///
    /// This is unsafe because the size of the passed-in buffer is
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

    /// The number of bits in the slice.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns whether there are no bits in the slice.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Converts a mutable bit slice to immutable.
    pub fn as_bit_slice(&self) -> BitSlice<'a, Block> {
        BitSlice {
            bits:   self.bits,
            offset: self.offset,
            len:    self.len,
            marker: PhantomData,
        }
    }
}

impl<'a, 'b, Block: BlockType> From<&'b BitSliceMut<'a, Block>> for BitSlice<'a, Block> {
    fn from(slice: &'b BitSliceMut<'a, Block>) -> Self {
        slice.as_bit_slice()
    }
}

impl<'a, Block: BlockType> From<&'a [Block]> for BitSlice<'a, Block> {
    fn from(slice: &'a [Block]) -> Self {
        BitSlice::from_slice(slice)
    }
}

impl<'a, Block: BlockType> From<&'a mut [Block]> for BitSliceMut<'a, Block> {
    fn from(slice: &'a mut [Block]) -> Self {
        BitSliceMut::from_slice(slice)
    }
}

unsafe fn get_bit_with_offset<Block: BlockType>(
    bits: *const Block, offset: u8, position: u64) -> bool {

    let address   = Address::new::<Block>(position + u64::from(offset));
    let ptr       = bits.offset(address.block_index as isize);
    let block     = ptr::read(ptr);
    block.get_bit(address.bit_offset)
}

unsafe fn set_bit_with_offset<Block: BlockType>(
    bits: *mut Block, offset: u8, position: u64, value: bool) {

    let address   = Address::new::<Block>(position + u64::from(offset));
    let ptr       = bits.offset(address.block_index as isize);
    let old_block = ptr::read(ptr);
    let new_block = old_block.with_bit(address.bit_offset, value);
    ptr::write(ptr, new_block);
}

unsafe fn get_block_with_offset<Block: BlockType>(
    bits: *const Block, offset: u8, len: u64, position: usize) -> Block {

    let value_len  = Block::block_bits(len, position);
    let value_mask = Block::low_mask(value_len);

    let block1 = ptr::read(bits.offset(position as isize));
    if offset == 0 {
        return block1 & value_mask;
    }

    let block2 = if position + 1 < Block::ceil_div_nbits(len + u64::from(offset)) {
        ptr::read(bits.offset(position as isize + 1))
    } else {
        Block::zero()
    };

    let shift1 = offset as usize;
    let shift2 = Block::nbits() - shift1;

    let chunk1 = block1.get_bits(shift1, shift2);
    let chunk2 = block2.get_bits(0, shift1) << shift2;

    (chunk1 | chunk2) & value_mask
}

unsafe fn set_block_with_offset<Block: BlockType>(
    bits: *mut Block, offset: u8, len: u64, position: usize, value: Block) {

    let start_bit     = Block::mul_nbits(position);
    let mut limit_bit = start_bit + Block::nbits() as u64;

    let ptr1          = bits.offset(position as isize);

    if offset == 0 && limit_bit <= len {
        ptr::write(ptr1, value);
        return;
    } else {
        limit_bit = cmp::min(limit_bit, len);
    }

    let shift1      = offset as usize;
    let shift2      = Block::nbits() - shift1;

    let bits_size1  = cmp::min((limit_bit - start_bit) as usize, shift2);
    let old_block1  = ptr::read(ptr1);
    let new_block1  = old_block1.with_bits(shift1, bits_size1, value);
    ptr::write(ptr1, new_block1);

    if position + 1 < Block::ceil_div_nbits(len + u64::from(offset)) {
        let ptr2        = ptr1.offset(1);
        let bits_size2  = cmp::min((limit_bit - Block::mul_nbits(position + 1)) as usize, shift1);
        let old_block2  = ptr::read(ptr2);
        let new_block2  = old_block2.with_bits(0, bits_size2, value >> shift2);
        ptr::write(ptr2, new_block2);
    }
}

impl<'a, Block: BlockType> Bits for BitSlice<'a, Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn get_bit(&self, position: u64) -> bool {
        assert!(position < self.bit_len(), "BitSlice::get_bit: out of bounds");

        unsafe {
            get_bit_with_offset(self.bits, self.offset, position)
        }
    }

    fn get_block(&self, position: usize) -> Block {
        assert!(position < self.block_len(), "BitSlice::get_block: out of bounds");

        unsafe {
            get_block_with_offset(self.bits, self.offset, self.len, position)
        }
    }
}

impl<'a, Block: BlockType> Bits for BitSliceMut<'a, Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn get_bit(&self, position: u64) -> bool {
        assert!(position < self.bit_len(), "BitSliceMut::get_bit: out of bounds");

        unsafe {
            get_bit_with_offset(self.bits, self.offset, position)
        }
    }

    fn get_block(&self, position: usize) -> Block {
        assert!(position < self.block_len(), "BitSliceMut::get_block: out of bounds");

        unsafe {
            get_block_with_offset(self.bits, self.offset, self.len, position)
        }
    }
}

impl<'a, Block: BlockType> BitsMut for BitSliceMut<'a, Block> {
    fn set_bit(&mut self, position: u64, value: bool) {
        assert!(position < self.bit_len(), "BitSliceMut::set_bit: out of bounds");

        unsafe {
            set_bit_with_offset(self.bits, self.offset, position, value);
        }
    }

    fn set_block(&mut self, position: usize, value: Block) {
        assert!(position < self.block_len(), "BitSliceMut::set_block: out of bounds");

        unsafe {
            set_block_with_offset(self.bits, self.offset, self.len, position, value);
        }
    }
}

impl_index_from_bits! {
    impl['a, Block: BlockType] Index<u64> for BitSlice<'a, Block>;
    impl['a, Block: BlockType] Index<u64> for BitSliceMut<'a, Block>;
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: Range<u64>) -> Self {
        assert!(range.start <= range.end, "BitSlice::slice: bad range");
        assert!(range.end <= self.len, "BitSlice::slice: out of bounds");

        let start_bits   = u64::from(self.offset) + range.start;
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

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: Range<u64>) -> Self {
        assert!(range.start <= range.end, "BitSliceMut::slice: bad range");
        assert!(range.end <= self.len, "BitSliceMut::slice: out of bounds");

        let start_bits   = u64::from(self.offset) + range.start;
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

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("BitSlice::slice: bad range");
        assert!(end < self.len, "BitSlice::slice: out of bounds");

        let start_bits   = u64::from(self.offset) + start;
        let start_block  = Block::div_nbits(start_bits);
        let start_offset = Block::mod_nbits(start_bits) as u8;

        BitSlice {
            bits:   unsafe { self.bits.offset(start_block as isize) },
            offset: start_offset,
            len:    end - start + 1,
            marker: PhantomData,
        }
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("BitSliceMut::slice: bad range");
        assert!(end < self.len, "BitSliceMut::slice: out of bounds");

        let start_bits   = u64::from(self.offset) + start;
        let start_addr   = Address::new::<Block>(start_bits);

        BitSliceMut {
            bits:   unsafe { self.bits.offset(start_addr.block_index as isize) },
            offset: start_addr.bit_offset as u8,
            len:    end - start + 1,
            marker: PhantomData,
        }
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self {
        let len = self.len;
        self.bit_slice(range.start .. len)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self {
        let len = self.len;
        self.bit_slice(range.start .. len)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeTo<u64>) -> Self {
        self.bit_slice(0 .. range.end)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeTo<u64>) -> Self {
        self.bit_slice(0 .. range.end)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self {
        self.bit_slice(0 .. range.end + 1)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self {
        self.bit_slice(0 .. range.end + 1)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for BitSlice<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, _: RangeFull) -> Self {
        self
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for BitSliceMut<'a, Block> {
    type Slice = Self;

    fn bit_slice(self, _: RangeFull) -> Self {
        self
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> Self::Slice {
        BitSlice::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> Self::Slice {
        BitSliceMut::from_slice(self).bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self::Slice {
        BitSlice::from_slice(self).bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self::Slice {
        BitSliceMut::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self::Slice {
        BitSlice::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self::Slice {
        BitSliceMut::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> Self::Slice {
        BitSlice::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> Self::Slice {
        BitSliceMut::from_slice(self).bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self::Slice {
        BitSlice::from_slice(self).bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self::Slice {
        BitSliceMut::from_slice(self).bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a [Block] {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> Self::Slice {
        BitSlice::from_slice(self)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a mut [Block] {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> Self::Slice {
        BitSliceMut::from_slice(self)
    }
}

impl<'a, Other: Bits> PartialEq<Other> for BitSlice<'a, Other::Block> {
    fn eq(&self, other: &Other) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

impl<'a, Block: BlockType> Eq for BitSlice<'a, Block> {}

impl<'a, Block: BlockType> PartialOrd for BitSlice<'a, Block> {
    fn partial_cmp(&self, other: &BitSlice<Block>) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, Block: BlockType> Ord for BitSlice<'a, Block> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let iter1 = BlockIter::new(*self);
        let iter2 = BlockIter::new(*other);
        (iter1).cmp(iter2)
    }
}

impl<'a, Other: Bits> PartialEq<Other> for BitSliceMut<'a, Other::Block> {
    fn eq(&self, other: &Other) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

impl<'a, Block: BlockType> Eq for BitSliceMut<'a, Block> {}

impl<'a, Block: BlockType> PartialOrd for BitSliceMut<'a, Block> {
    fn partial_cmp(&self, other: &BitSliceMut<Block>) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, Block: BlockType> Ord for BitSliceMut<'a, Block> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_bit_slice().cmp(&other.as_bit_slice())
    }
}

impl<'a, Block: BlockType + hash::Hash> hash::Hash for BitSlice<'a, Block> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.bit_len());
        for block in BlockIter::new(self) {
            block.hash(state);
        }
    }
}

impl<'a, Block: BlockType + hash::Hash> hash::Hash for BitSliceMut<'a, Block> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_bit_slice().hash(state);
    }
}

impl<'a, Block: BlockType> fmt::Debug for BitSlice<'a, Block> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "bit_vec![")?;
        if !self.is_empty() {
            write!(f, "{}", self.get_bit(0))?;
        }
        for i in 1 .. self.len() {
            write!(f, ", {}", self.get_bit(i))?;
        }
        write!(f, "]")
    }
}

impl<'a, Block: BlockType> fmt::Debug for BitSliceMut<'a, Block> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_bit_slice().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use BitVec;
    use super::*;

    #[test]
    fn bit_slice_from_slice() {
        let mut bytes = [0b00001111u8];
        {
            let mut bs = BitSliceMut::from_slice(&mut bytes);
            assert_eq!( bs.get_block(0), 0b00001111 );
            bs.set_bit(1, false);
            assert_eq!( bs.get_block(0), 0b00001101 );
        }

        assert_eq!( bytes[0], 0b00001101 );
    }

    #[test]
    fn bit_slice_index() {
        let mut bytes = [0b00001111u8];
        {
            let bs = BitSlice::from_slice(&bytes);
            assert_eq!( bs[3], true );
            assert_eq!( bs[4], false );
        }
        {
            let bs = BitSliceMut::from_slice(&mut bytes);
            assert_eq!( bs[3], true );
            assert_eq!( bs[4], false );
        }
    }

    #[test]
    fn bit_slice_update_across_blocks() {
        let mut bv: BitVec<u8> = bit_vec![ true; 20 ];
        bv.set_bit(3, false);
        bv.set_bit(7, false);

        {
            let mut slice: BitSliceMut<u8> = (&mut bv).bit_slice(4..12);
            slice.set_bit(1, false);
            slice.set_bit(5, false);
        }

        assert!(  bv[0] );
        assert!(  bv[1] );
        assert!(  bv[2] );
        assert!( !bv[3] );
        assert!(  bv[4] );
        assert!( !bv[5] );
        assert!(  bv[6] );
        assert!( !bv[7] );
        assert!(  bv[8] );
        assert!( !bv[9] );
    }

    #[test]
    fn debug_for_bit_slice() {
        let slice = [0b00110101u8];
        let bs = BitSlice::from_slice(&slice);
        let exp = "bit_vec![true, false, true, false, true, true, false, false]";
        let act = format!("{:?}", bs);
        assert_eq!( act, exp );
    }

    #[cfg(inclusive_range)]
    #[test]
    fn range_to_inclusive() {
        use BitSliceable;

        let base = [0b00110101u8];
        let slice = base.bit_slice(::std::ops::RangeToInclusive { end: 4 });
        assert_eq!( slice.len(), 5 );
    }
}

