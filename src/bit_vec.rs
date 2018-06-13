use std::cmp::{max, Ordering};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

use iter::BlockIter;
use super::storage::*;
use super::slice::*;
use super::traits::*;

/// A bit-vector, akin to `Vec<bool>` but packed.
///
/// `BitVec` stores its bits in an array of `Block`s, where `Block` is given as a type parameter
/// that defaults to `usize`. You might find that a different `Block` size is preferable, but
/// only benchmarking will tell.
///
/// Several useful methods are exported in traits, rather than inherent to `BitVec`. In
/// particular, see:
///
///   - [`Bits::get_bit`](trait.Bits.html#method.get_bit) and
///   - [`BitsMut::set_bit`](trait.BitsMut.html#method.set_bit).
///
/// You will likely want to `use` these traits (or `bv::*`) when you use `BitVec`.
///
/// # Examples
///
/// ```
/// use bv::BitVec;
///
/// let mut bv: BitVec = BitVec::new();
/// assert_eq!(bv.len(), 0);
///
/// bv.push(true);
/// bv.push(false);
/// bv.push(true);
/// assert_eq!(bv.len(), 3);
///
/// assert_eq!(bv[0], true);
/// assert_eq!(bv[1], false);
/// assert_eq!(bv[2], true);
/// ```
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BitVec<Block = usize> {
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

impl<Block: BlockType> Default for BitVec<Block> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Block: BlockType> BitVec<Block> {
    /// Creates a new, empty bit-vector with a capacity of one block.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitVec;
    ///
    /// let mut bv: BitVec = BitVec::new();
    /// assert_eq!(bv.len(), 0);
    ///
    /// bv.push(true);
    /// bv.push(false);
    /// bv.push(true);
    /// assert_eq!(bv.len(), 3);
    ///
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], false);
    /// assert_eq!(bv[2], true);
    /// ```
    pub fn new() -> Self {
        Self::with_block_capacity(1)
    }

    /// Creates a new, empty bit-vector with the given bit capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitVec;
    ///
    /// let mut bv: BitVec<u16> = BitVec::with_capacity(20);
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
    /// use bv::BitVec;
    ///
    /// let mut bv: BitVec<u16> = BitVec::with_block_capacity(8);
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
    /// let mut bv: BitVec<u64> = BitVec::new_fill(false, 100);
    ///
    /// assert_eq!( bv.get(0), false );
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
        BitVec {
            bits: vec![ init; nblocks ].into_boxed_slice(),
            len:  Block::mul_nbits(nblocks),
        }
    }

    /// Creates a new `BitVec` from any value implementing the `Bits` trait with
    /// the same block type.
    pub fn from_bits<B: Bits<Block = Block>>(bits: B) -> Self {
        let mut result: Self = Self::with_capacity(bits.bit_len());

        for i in 0..bits.block_len() {
            result.push_block(bits.get_block(i));
        }

        result.resize(bits.bit_len(), false);
        result
    }

    /// The number of bits in the bit-vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitVec;
    ///
    /// let mut bv: BitVec = BitVec::new();
    /// assert_eq!(bv.len(), 0);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 1);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 2);
    /// bv.push(false);
    /// assert_eq!(bv.len(), 3);
    /// ```
    #[inline]
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
    /// let mut bv: BitVec<u64> = BitVec::new_fill(false, 100);
    ///
    /// assert_eq!( bv.len(), 100 );
    /// assert_eq!( bv.block_len(), 2 );
    /// ```
    pub fn block_len(&self) -> usize {
        Block::ceil_div_nbits(self.len())
    }

    /// The capacity of the bit-vector in bits.
    ///
    /// This is the number of bits that can be held without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec<u64> = bit_vec![false; 100];
    ///
    /// assert_eq!( bv.len(), 100 );
    /// assert_eq!( bv.capacity(), 128 );
    /// ```
    ///
    /// Note that this example holds because `bit_vec!` does not introduces excess
    /// capacity.
    pub fn capacity(&self) -> u64 {
        Block::mul_nbits(self.block_capacity())
    }

    /// The capacity of the bit-vector in blocks.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec<u64> = BitVec::with_capacity(250);
    ///
    /// assert_eq!( bv.len(), 0 );
    /// assert_eq!( bv.block_len(), 0 );
    /// assert_eq!( bv.capacity(), 256 );
    /// assert_eq!( bv.block_capacity(), 4 );
    /// ```
    ///
    /// Note that this example holds because `bit_vec!` does not introduces excess
    /// capacity.
    pub fn block_capacity(&self) -> usize {
        self.bits.len()
    }

    /// Adjust the capacity to hold at least `additional` additional bits.
    ///
    /// May reserve more to avoid frequent reallocations.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ false, false, true ];
    /// assert_eq!( bv.capacity(), 32 );
    /// bv.reserve(100);
    /// assert!( bv.capacity() >= 103 );
    /// ```
    pub fn reserve(&mut self, additional: u64) {
        let old_cap = self.capacity();
        self.reserve_exact(max(1, max(additional, old_cap)));
    }

    /// Adjust the capacity to hold at least `additional` additional blocks.
    ///
    /// May reserve more to avoid frequent reallocations.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ false, false, true ];
    /// assert_eq!( bv.block_capacity(), 1 );
    /// bv.block_reserve(3);
    /// assert!( bv.block_capacity() >= 4 );
    /// ```
    pub fn block_reserve(&mut self, additional: usize) {
        let old_cap = self.block_capacity();
        self.block_reserve_exact(max(1, max(additional, old_cap)));
    }

    /// Adjust the capacity to hold at least `additional` additional bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ false, false, true ];
    /// assert_eq!( bv.capacity(), 32 );
    /// bv.reserve_exact(100);
    /// assert_eq!( bv.capacity(), 128 );
    /// ```
    pub fn reserve_exact(&mut self, additional: u64) {
        let new_cap = Block::ceil_div_nbits(self.len() + additional);
        if new_cap > self.block_capacity() {
            self.bits = copy_resize(&self.bits, new_cap);
        }
    }

    /// Adjusts the capacity to at least `additional` blocks beyond those used.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ false, false, true ];
    /// assert_eq!( bv.block_capacity(), 1 );
    /// bv.block_reserve_exact(3);
    /// assert_eq!( bv.block_capacity(), 4 );
    /// ```
    pub fn block_reserve_exact(&mut self, additional: usize) {
        let new_cap = self.block_len() + additional;
        if new_cap > self.block_capacity() {
            self.bits = copy_resize(&self.bits, new_cap);
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitVec;
    ///
    /// let mut bv: BitVec<u8> = BitVec::new();
    ///
    /// for i in 0 .. 23 {
    ///     bv.push(i % 3 == 0);
    /// }
    ///
    /// assert!(bv.capacity() >= 24);
    ///
    /// bv.shrink_to_fit();
    /// assert_eq!(bv.capacity(), 24);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        if self.block_capacity() > self.block_len() {
            self.bits = copy_resize(&self.bits, self.block_len());
        }
    }

    /// Converts the vector into `Box<[Block]>`.
    ///
    /// Note that this will *not* drop any excess capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec<u8> = bit_vec![true, true, false, false, true, false, true, false];
    /// let bs = bv.into_boxed_slice();
    ///
    /// assert!( bs.len() >= 1 );
    /// assert_eq!( bs[0], 0b01010011 );
    /// ```
    pub fn into_boxed_slice(self) -> Box<[Block]> {
        self.bits
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// Note that this method has no effect on the capacity of the bit-vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut v1: BitVec = bit_vec![ true, true, false, false ];
    /// let     v2: BitVec = bit_vec![ true, true ];
    ///
    /// assert_ne!( v1, v2 );
    ///
    /// v1.truncate(2);
    ///
    /// assert_eq!( v1, v2 );
    /// ```
    pub fn truncate(&mut self, len: u64) {
        if len < self.len {
            self.len = len;
        }
    }

    /// Resizes the bit-vector, filling with `value` if it has to grow.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let     v1: BitVec = bit_vec![ true, true, false, false ];
    /// let mut v2: BitVec = bit_vec![ true, true ];
    /// let mut v3: BitVec = bit_vec![ true, true ];
    ///
    /// v2.resize(4, false);
    /// v3.resize(4, true);
    ///
    /// assert_eq!( v1, v2 );
    /// assert_ne!( v1, v3 );
    /// ```
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

    /// Gets a slice to a `BitVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let bv: BitVec = bit_vec![true, false, true];
    /// let slice = bv.as_slice();
    ///
    /// assert_eq!( slice.len(), 3 );
    /// assert_eq!( slice[0], true );
    /// assert_eq!( slice[1], false );
    /// assert_eq!( slice[2], true );
    /// ```
    pub fn as_slice(&self) -> BitSlice<Block> {
        unsafe {
            BitSlice::from_raw_parts(self.bits.as_ptr(), 0, self.len)
        }
    }

    /// Gets a mutable slice to a `BitVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec = bit_vec![true, false, true];
    ///
    /// {
    ///     let mut slice = bv.as_mut_slice();
    ///     slice.set_bit(1, true);
    /// }
    ///
    /// assert_eq!( bv[1], true );
    /// ```
    pub fn as_mut_slice(&mut self) -> BitSliceMut<Block> {
        unsafe {
            BitSliceMut::from_raw_parts(self.bits.as_mut_ptr(), 0, self.len)
        }
    }

    /// Gets the value of the bit at the given position.
    ///
    /// This is an alias for [`Bits::get_bit`].
    ///
    /// # Panics
    ///
    /// If the position is out of bounds.
    ///
    /// [`Bits::get_bit`]: ../trait.Bits.html#get_bit.method
    pub fn get(&mut self, position: u64) -> bool {
        self.get_bit(position)
    }

    /// Sets the value of the bit at the given position.
    ///
    /// This is an alias for [`BitsMut::set_bit`].
    ///
    /// # Panics
    ///
    /// If the position is out of bounds.
    ///
    /// [`BitsMut::set_bit`]: ../trait.BitsMut.html#set_bit.method
    pub fn set(&mut self, position: u64, value: bool) {
        self.set_bit(position, value);
    }

    /// Adds the given `bool` to the end of the bit-vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv0: BitVec = bit_vec![ ];
    /// let     bv1: BitVec = bit_vec![ true ];
    /// let     bv2: BitVec = bit_vec![ true, false ];
    /// let     bv3: BitVec = bit_vec![ true, false, true ];
    ///
    /// assert_ne!( bv0, bv1 );
    /// assert_ne!( bv0, bv2 );
    /// assert_ne!( bv0, bv3 );
    ///
    /// bv0.push(true);
    /// assert_eq!( bv0, bv1 );
    ///
    /// bv0.push(false);
    /// assert_eq!( bv0, bv2 );
    ///
    /// bv0.push(true);
    /// assert_eq!( bv0, bv3 );
    /// ```
    pub fn push(&mut self, value: bool) {
        if self.len() == self.capacity() - 1 {
            self.reserve(1);
        }

        let old_len = self.len;
        self.len = old_len + 1;
        self.set_bit(old_len, value);
    }

    /// Removes and returns the last element of the bit-vector, or `None` if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec = bit_vec![ true, false, true ];
    /// assert_eq!( bv.pop(), Some(true) );
    /// assert_eq!( bv.pop(), Some(false) );
    /// assert_eq!( bv.pop(), Some(true) );
    /// assert_eq!( bv.pop(), None );
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ true ];
    /// assert_eq!( bv.len(), 1 );
    /// assert_eq!( bv.capacity(), 32 );
    /// bv.clear();
    /// assert_eq!( bv.len(), 0 );
    /// assert_eq!( bv.capacity(), 32 );
    /// ```
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Does the bit-vector have no elements?
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let mut bv: BitVec<u32> = bit_vec![ true ];
    /// assert!( !bv.is_empty() );
    /// bv.clear();
    /// assert!(  bv.is_empty() );
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<Block: BlockType> Bits for BitVec<Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len()
    }

    fn get_block(&self, position: usize) -> Block {
        if position + 1 == self.block_len() {
            self.bits[position].get_bits(0, Block::last_block_bits(self.bit_len()))
        } else {
            self.bits[position]
        }
    }
}

impl<Block: BlockType> BitsMut for BitVec<Block> {
    fn set_block(&mut self, position: usize, value: Block) {
        self.bits[position] = value;
    }
}

impl<Block: BlockType> BitsPush for BitVec<Block> {
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

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<Range<u64>> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: Range<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeInclusive<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeInclusive<u64>> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeInclusive<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFrom<u64>> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeFrom<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeTo<u64>> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeTo<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> BitSlice<'a, Block> {
        self.as_slice().bit_slice(range)
    }
}

#[cfg(inclusive_range)]
impl<'a, Block: BlockType> BitSliceable<RangeToInclusive<u64>> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> BitSliceMut<'a, Block> {
        self.as_mut_slice().bit_slice(range)
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a BitVec<Block> {
    type Slice = BitSlice<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> BitSlice<'a, Block> {
        self.as_slice()
    }
}

impl<'a, Block: BlockType> BitSliceable<RangeFull> for &'a mut BitVec<Block> {
    type Slice = BitSliceMut<'a, Block>;

    fn bit_slice(self, _: RangeFull) -> BitSliceMut<'a, Block> {
        self.as_mut_slice()
    }
}

impl_index_from_bits! {
    impl[Block: BlockType] Index<u64> for BitVec<Block>;
}

impl<Other: Bits> PartialEq<Other> for BitVec<Other::Block> {
    fn eq(&self, other: &Other) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

impl<Block: BlockType> PartialOrd for BitVec<Block> {
    fn partial_cmp(&self, other: &BitVec<Block>) -> Option<Ordering> {
        let iter1 = BlockIter::new(self);
        let iter2 = BlockIter::new(other);
        iter1.partial_cmp(iter2)
    }
}

impl<Block: BlockType> Eq for BitVec<Block> {}

impl<Block: BlockType> Ord for BitVec<Block> {
    fn cmp(&self, other: &Self) -> Ordering {
        let iter1 = BlockIter::new(self);
        let iter2 = BlockIter::new(other);
        iter1.cmp(iter2)
    }
}

impl<Block: BlockType + Hash> Hash for BitVec<Block> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<Block: BlockType> fmt::Debug for BitVec<Block> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bit_slicing() {
        let v: BitVec<u8> = bit_vec![ false, true, true, false, true, false, false, true,
                                      true, false, false, true, false, true, true, false ];
        assert!( !v.get_bit(0) );
        assert!(  v.get_bit(1) );
        assert!(  v.get_bit(2) );
        assert!( !v.get_bit(3) );

        let w = v.bit_slice(2..14);
        assert_eq!( w.bit_len(), 12 );

        assert!(  w.get_bit(0) );
        assert!( !w.get_bit(1) );

        assert_eq!( w.get_bits(2, 4), 0b00001001 );
        assert_eq!( w.get_bits(2, 5), 0b00011001 );
        assert_eq!( w.get_bits(2, 8), 0b10011001 );
        assert_eq!( w.get_bits(3, 8), 0b01001100 );

        assert_eq!( w.get_block(0), 0b01100101 );
        assert_eq!( w.get_block(1), 0b00001010 );
    }

    #[test]
    fn resize() {
        let mut v: BitVec<u8> = bit_vec![ true; 13 ];
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
        let mut v: BitVec<u8> = BitVec::with_capacity(100);
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
        let v: BitVec<u8> = bit_vec![ true, false, true ];
        assert_eq!( v.capacity(), 8 );
        let bs = v.into_boxed_slice();
        assert_eq!( bs.len(), 1 );
        assert_eq!( bs[0], 0b00000101 );
    }

    #[test]
    fn truncate() {
        let mut v: BitVec<u8> = BitVec::new_fill(true, 80);
        assert_eq!( v.len(), 80 );
        assert_eq!( v.get_bit(34), true );

        v.truncate(45);
        assert_eq!( v.len(), 45 );
        assert_eq!( v.get_bit(34), true );
    }

    #[test]
    fn as_mut_slice() {
        let mut v: BitVec<u8> = BitVec::new_fill(true, 77);
        let w = v.as_mut_slice();
        assert_eq!( w.len(), 77 );
        assert_eq!( w.get_block(0), 0b11111111 );
    }

    #[test]
    fn pop() {
        let mut v: BitVec<u8> = bit_vec![true, false, true];
        assert_eq!( v.pop(), Some(true) );
        assert_eq!( v.pop(), Some(false) );
        assert_eq!( v.pop(), Some(true) );
        assert_eq!( v.pop(), None );
    }

    #[test]
    fn clear_and_is_empty() {
        let mut v: BitVec<u8> = bit_vec![true, false, true];
        assert_eq!( v.len(), 3 );
        assert!( !v.is_empty() );
        v.clear();
        assert_eq!( v.len(), 0 );
        assert!( v.is_empty() );
    }

    #[test]
    fn push_bit_and_pop_bit() {
        let mut v: BitVec<u8> = BitVec::new();
        v.push_bit(true);
        v.push_bit(false);
        assert_eq!( v.pop_bit(), Some(false) );
        assert_eq!( v.pop_bit(), Some(true) );
        assert_eq!( v.pop_bit(), None );
    }

    #[test]
    fn set_through_slice() {
        let mut v: BitVec<u8> = bit_vec![true, false, true];

        {
            let mut w = v.as_mut_slice().bit_slice(1..2);
            assert_eq!(w.get_block(0), 0);
            w.set_bit(0, true);
        }

        assert_eq!(v, bit_vec![true, true, true] );
    }

    #[test]
    fn set_bits_one_block_fastpath() {
        let mut v: BitVec<u8> = bit_vec![false; 8];
        v.set_bits(2, 4, 0b1111);
        assert_eq!( v.get_block(0), 0b00111100 );
    }

    #[test]
    fn from_bits() {
        let mut bits = vec![true; 20];
        bits[3] = false;
        let bv = BitVec::from_bits(&bits);
        assert_eq!( bv.len(), 20 );
        assert!(  bv[0] );
        assert!(  bv[1] );
        assert!(  bv[2] );
        assert!( !bv[3] );
        assert!(  bv[4] );
        assert!(  bv[19] );
    }

    #[test]
    fn from_bits_slice() {
        let mut bits: BitVec = bit_vec![true; 20];
        bits.set_bit(3, false);
        let slice = bits.bit_slice(1..);
        let bv = BitVec::from_bits(&slice);
        assert_eq!( bv.len(), 19 );
        assert!(  bv[0] );
        assert!(  bv[1] );
        assert!( !bv[2] );
        assert!(  bv[3] );
        assert!(  bv[18] );
    }

    #[test]
    fn disequality() {
        let bv1: BitVec = bit_vec![true, true, false];
        let bv2         = bit_vec![true, true];
        assert_ne!( bv1, bv2 );
    }

    #[test]
    fn mixed_equality() {
        let bv: BitVec<u8> = bit_vec![true, false, true];
        let array: &[bool] = &[true, false, true];
        assert_eq!( bv, array );
    }
}
