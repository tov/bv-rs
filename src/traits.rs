use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};
use super::storage::{BlockType, Address};

/// Read-only bit vector operations.
///
/// Minimal complete definition is:
///
///   - `bit_len`,
///   - `bit_offset`, and
///   - `get_bit` or `get_block`, since each is defined in terms of the other.
///
/// Note that `get_block` in terms of `get_bit` is inefficient, and thus
/// you should implement `get_block` directly if possible.
pub trait Bits {
    /// The underlying block type used to store the bits of the vector.
    type Block: BlockType;

    /// The length of the slice in bits.
    fn bit_len(&self) -> u64;

    /// The number of bits into the first block that the bit vector starts.
    /// Must be less than `Block::nbits()`.
    fn bit_offset(&self) -> u8;

    /// The length of the slice in blocks.
    fn block_len(&self) -> usize {
        Self::Block::ceil_div_nbits(self.bit_len() + u64::from(self.bit_offset()))
    }

    /// Gets the bit at `position`
    ///
    /// The default implementation calls `get_block` and masks out the
    /// correct bit.
    ///
    /// # Panics
    ///
    /// Panics if `position` is out of bounds.
    fn get_bit(&self, position: u64) -> bool {
        assert!(position < self.bit_len(), "Bits::get_bit: out of bounds");

        let address = Address::new::<Self::Block>(position + u64::from(self.bit_offset()));
        let block = self.get_block(address.block_index);
        block.get_bit(address.bit_offset)
    }

    /// Gets the block at `position`
    ///
    /// The bits are laid out `Block::nbits()` per block, with the notional
    /// zeroth bit in the least significant position. If `self.bit_len()` is
    /// not a multiple of `Block::nbits()` then the last block will
    /// contain extra bits that are not part of the bit vector.
    ///
    /// The default implementation assembles a block by reading each of its
    /// bits. Consider it a slow reference implementation, and override it.
    ///
    /// # Panics
    ///
    /// Panics if `position` is out of bounds.
    fn get_block(&self, position: usize) -> Self::Block {
        assert!(position < self.block_len(),
                format!("Bits::get_block: out of bounds ({}/{})",
                        position, self.block_len()));

        let bit_position = position as u64 * Self::Block::nbits() as u64;

        let mut result = Self::Block::zero();
        let mut mask = Self::Block::one();

        for i in 0 .. Self::Block::nbits() as u64 {
            if bit_position + i >= u64::from(self.bit_offset())
                && bit_position + i - u64::from(self.bit_offset()) < self.bit_len()
                && self.get_bit(bit_position + i - u64::from(self.bit_offset())) {
                result = result | mask;
            }
            mask = mask << 1;
        }

        result
    }

    /// Gets `count` bits starting at bit index `start`, interpreted as a
    /// little-endian integer.
    ///
    /// # Panics
    ///
    /// Panics if the bit span goes out of bounds.
    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        let limit = start + count as u64;
        assert!(limit <= self.bit_len(), "Bits::get_bits: out of bounds");

        let address = Address::new::<Self::Block>(start + u64::from(self.bit_offset()));
        let margin = Self::Block::nbits() - address.bit_offset;

        if margin >= count {
            let block = self.get_block(address.block_index);
            return block.get_bits(address.bit_offset, count)
        }

        let extra = count - margin;

        let block1 = self.get_block(address.block_index);
        let block2 = self.get_block(address.block_index + 1);

        let low_bits = block1.get_bits(address.bit_offset, margin);
        let high_bits = block2.get_bits(0, extra);

        (high_bits << margin) | low_bits
    }
}

/// Mutable bit vector operations that don’t affect the length.
///
/// Minimal complete definition is `set_bit` or `set_block`, since each
/// is defined in terms of the other. Note that `set_block` in terms of
/// `set_bit` is inefficient, and thus you should implement `set_block`
/// directly if possible.
pub trait BitsMut: Bits {
    /// Sets the bit at `position` to `value`.
    ///
    /// The default implementation uses `get_block` and `set_block`.
    ///
    /// # Panics
    ///
    /// Panics if `position` is out of bounds.
    fn set_bit(&mut self, position: u64, value: bool) {
        assert!(position < self.bit_len(), "BitsMut::set_bit: out of bounds");

        let address = Address::new::<Self::Block>(position + u64::from(self.bit_offset()));
        let old_block = self.get_block(address.block_index);
        let new_block = old_block.with_bit(address.bit_offset, value);
        self.set_block(address.block_index, new_block);
    }

    /// Sets the block at `position` to `value`.
    ///
    /// The bits are laid out `Block::nbits()` per block, with the notional
    /// zeroth bit in the least significant position. If `self.bit_len()` is
    /// not a multiple of `Block::nbits()` then the last block will
    /// contain extra bits that are not part of the bit vector. Implementations
    /// of `set_block` should not change those trailing bits.
    ///
    /// The default implementation sets a block by setting each of its bits
    /// in turn. Consider it a slow reference implementation, and override it.
    ///
    /// # Panics
    ///
    /// Panics if `position` is out of bounds.
    fn set_block(&mut self, position: usize, mut value: Self::Block) {
        let start = if position == 0 && self.bit_offset() > 0 {
            value = value >> self.bit_offset() as usize;
            u64::from(self.bit_offset())
        } else {
            0
        };

        let limit = if position + 1 == self.block_len() {
            Self::Block::last_block_bits(self.bit_len() + u64::from(self.bit_offset()))
        } else {
            Self::Block::nbits()
        };

        let offset = Self::Block::mul_nbits(position);
        let bit_offset = u64::from(self.bit_offset());

        for i in start .. limit as u64 {
            let bit = value & Self::Block::one() != Self::Block::zero();
            self.set_bit(offset + i - bit_offset, bit);
            value = value >> 1;
        }
    }

    /// Sets `count` bits starting at bit index `start`, interpreted as a
    /// little-endian integer.
    ///
    /// # Panics
    ///
    /// Panics if the bit span goes out of bounds.
    fn set_bits(&mut self, start: u64, count: usize, value: Self::Block) {
        let limit = start + count as u64;
        assert!(limit <= self.bit_len(), "BitsMut::set_bits: out of bounds");

        let address = Address::new::<Self::Block>(start + u64::from(self.bit_offset()));
        let margin = Self::Block::nbits() - address.bit_offset;

        if margin >= count {
            let old_block = self.get_block(address.block_index);
            let new_block = old_block.with_bits(address.bit_offset, count, value);
            self.set_block(address.block_index, new_block);
            return;
        }

        let extra = count - margin;

        let old_block1 = self.get_block(address.block_index);
        let old_block2 = self.get_block(address.block_index + 1);

        let high_bits = value >> margin;

        let new_block1 = old_block1.with_bits(address.bit_offset,
                                              margin, value);
        let new_block2 = old_block2.with_bits(0, extra, high_bits);
        self.set_block(address.block_index, new_block1);
        self.set_block(address.block_index + 1, new_block2);
    }
}

/// Bit vector operations that change the length.
pub trait BitsPush: BitsMut {
    /// Adds the given bit to the end of the bit vector.
    fn push_bit(&mut self, value: bool);

    /// Removes and returns the last bit, if any.
    fn pop_bit(&mut self) -> Option<bool>;

    /// Pushes `value` 0 or more times until the size of the bit
    /// vector is block-aligned.
    fn align_block(&mut self, value: bool) {
        while Self::Block::mod_nbits(self.bit_len() + u64::from(self.bit_offset())) != 0 {
            self.push_bit(value);
        }
    }

    /// Pushes the given block onto the end of the bit vector.
    ///
    /// If the end of the bit vector is not currently block-aligned,
    /// it pads with 0s up to the next block before pushing.
    ///
    /// The default implementation pushes the block one bit at a time;
    /// override it with something more efficient.
    fn push_block(&mut self, mut value: Self::Block) {
        self.align_block(false);

        for _ in 0 .. Self::Block::nbits() {
            self.push_bit(value & Self::Block::one() != Self::Block::zero());
            value = value >> 1;
        }
    }
}

/// Types that support (re-)slicing by ranges.
pub trait BitSliceable<Range> {
    /// The type of the slice.
    type Slice;

    /// (Re-)slices the given object.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::*;
    ///
    /// let array = [0b01010011u16];
    /// let slice = BitSlice::from_slice(&array);
    ///
    /// assert_eq!( slice.bit_slice(1..3), slice.bit_slice(4..6) );
    /// assert_eq!( slice.bit_slice(1..3), slice.bit_slice(6..8) );
    ///
    /// assert_ne!( slice.bit_slice(2..4), slice.bit_slice(6..8) );
    /// assert_eq!( slice.bit_slice(2..4), slice.bit_slice(7..9) );
    /// ```
    fn bit_slice(self, range: Range) -> Self::Slice;
}

impl<Block: BlockType> Bits for [Block] {
    type Block = Block;

    #[inline]
    fn bit_len(&self) -> u64 {
        u64::from(Block::mul_nbits(self.len()))
    }

    #[inline]
    fn bit_offset(&self) -> u8 {
        0
    }

    #[inline]
    fn block_len(&self) -> usize {
        self.len()
    }

    #[inline]
    fn get_block(&self, position: usize) -> Block {
        self[position]
    }
}

impl<Block: BlockType> BitsMut for [Block] {
    #[inline]
    fn set_block(&mut self, position: usize, value: Block) {
        self[position] = value;
    }
}

impl Bits for [bool] {
    type Block = u8; // This is bogus

    #[inline]
    fn bit_len(&self) -> u64 {
        self.len() as u64
    }

    #[inline]
    fn bit_offset(&self) -> u8 {
        0
    }

    fn get_bit(&self, position: u64) -> bool {
        self[position.to_usize().expect("Vec<bool>::get_bit: overflow")]
    }
}

impl BitsMut for [bool] {
    fn set_bit(&mut self, position: u64, value: bool) {
        let position = position.to_usize()
            .expect("Vec<bool>::set_bit: overflow");
        self[position] = value;
    }
}

impl Bits for Vec<bool> {
    type Block = u8;

    #[inline]
    fn bit_len(&self) -> u64 {
        self.as_slice().bit_len()
    }

    #[inline]
    fn bit_offset(&self) -> u8 {
        self.as_slice().bit_offset()
    }

    #[inline]
    fn get_bit(&self, position: u64) -> bool {
        self.as_slice().get_bit(position)
    }
}

impl BitsMut for Vec<bool> {
    #[inline]
    fn set_bit(&mut self, position: u64, value: bool) {
        self.as_mut_slice().set_bit(position, value)
    }
}

impl BitsPush for Vec<bool> {
    fn push_bit(&mut self, value: bool) {
        self.push(value);
    }

    fn pop_bit(&mut self) -> Option<bool> {
        self.pop()
    }
}

impl<'a> BitSliceable<Range<usize>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: Range<usize>) -> &'a [bool] {
        &self[range]
    }
}

impl<'a> BitSliceable<Range<usize>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: Range<usize>) -> &'a mut [bool] {
        &mut self[range]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<usize>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeInclusive<usize>) -> &'a [bool] {
        &self[range]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<usize>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeInclusive<usize>) -> &'a mut [bool] {
        &mut self[range]
    }
}

impl<'a> BitSliceable<RangeFrom<usize>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeFrom<usize>) -> &'a [bool] {
        &self[range]
    }
}

impl<'a> BitSliceable<RangeFrom<usize>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeFrom<usize>) -> &'a mut [bool] {
        &mut self[range]
    }
}

impl<'a> BitSliceable<RangeTo<usize>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeTo<usize>) -> &'a [bool] {
        &self[range]
    }
}

impl<'a> BitSliceable<RangeTo<usize>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeTo<usize>) -> &'a mut [bool] {
        &mut self[range]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<usize>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeToInclusive<usize>) -> &'a [bool] {
        &self[range]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<usize>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeToInclusive<usize>) -> &'a mut [bool] {
        &mut self[range]
    }
}

impl<'a> BitSliceable<RangeFull> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, _: RangeFull) -> &'a [bool] {
        self
    }
}

impl<'a> BitSliceable<RangeFull> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, _: RangeFull) -> &'a mut [bool] {
        self
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vec_u8_is_bit_vec() {
        let v = vec![0b01001000u8, 0b11100011u8];
        assert!( !v.get_bit(0) );
        assert!( !v.get_bit(1) );
        assert!( !v.get_bit(2) );
        assert!(  v.get_bit(3) );
        assert!( !v.get_bit(4) );
        assert!( !v.get_bit(5) );
        assert!(  v.get_bit(6) );
        assert!( !v.get_bit(7) );
        assert!(  v.get_bit(8) );
        assert!(  v.get_bit(9) );
        assert!( !v.get_bit(10) );
        assert!( !v.get_bit(11) );
        assert!( !v.get_bit(12) );
        assert!(  v.get_bit(13) );
        assert!(  v.get_bit(14) );
        assert!(  v.get_bit(15) );

        assert_eq!( v.get_bits(4, 8), 0b00110100u8 );
    }

    #[test]
    fn vec_u8_is_bit_vec_mut() {
        let mut v = vec![0b01001000u8, 0b11100011u8];
        assert!( !v.get_bit(0) );
        v.set_bit(0, true);
        assert!(  v.get_bit(0) );
        assert!( !v.get_bit(1) );
        v.set_bit(1, true);
        assert!(  v.get_bit(1) );
        assert!( !v.get_bit(10) );
        v.set_bit(10, true);
        assert!(  v.get_bit(10) );

        v.set_bits(4, 8, 0b11110000);

        assert!( !v.get_bit(4) );
        assert!( !v.get_bit(5) );
        assert!( !v.get_bit(6) );
        assert!( !v.get_bit(7) );
        assert!(  v.get_bit(8) );
        assert!(  v.get_bit(9) );
        assert!(  v.get_bit(10) );
        assert!(  v.get_bit(11) );
    }

    #[test]
    fn bogus_get_bits_vec_bool_works_okay() {
        let v = vec![ true, false, false, true, false, true, true, false,
                      false, true, true, false, true, false, false, true ];

        assert_eq!( v.bit_len(), 16 );
        assert_eq!( v.bit_offset(), 0 );
        assert_eq!( v.block_len(), 2 );

        assert!(  v.get_bit(0) );
        assert!( !v.get_bit(1) );
        assert!( !v.get_bit(2) );
        assert!(  v.get_bit(3) );

        assert_eq!( v.get_bits(0, 8), 0b01101001 );
        assert_eq!( v.get_bits(0, 7), 0b01101001 );
        assert_eq!( v.get_bits(0, 6), 0b00101001 );

        assert_eq!( v.get_bits(3, 5), 0b00001101 );
        assert_eq!( v.get_bits(3, 6), 0b00001101 );
        assert_eq!( v.get_bits(3, 7), 0b01001101 );
        assert_eq!( v.get_bits(3, 8), 0b11001101 );
        assert_eq!( v.get_bits(4, 8), 0b01100110 );
        assert_eq!( v.get_bits(5, 8), 0b10110011 );
        assert_eq!( v.get_bits(6, 8), 0b01011001 );
        assert_eq!( v.get_bits(7, 8), 0b00101100 );
        assert_eq!( v.get_bits(8, 8), 0b10010110 );
    }

    #[test]
    #[should_panic]
    fn bogus_get_bits_vec_bool_oob() {
        let v = vec![ false; 16 ];
        v.get_bits(9, 8);
    }

    #[test]
    #[should_panic]
    fn get_block_oob() {
        let v = vec![ false; 16 ];
        v.get_block(2);
    }

    #[test]
    fn bit_slicing() {
        let v = vec![ 0b10010110u8, 0b01101001u8 ];
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
    fn set_block() {
        let mut v = vec![ false; 16 ];

        assert_eq!( v.get_block(0), 0b00000000 );
        assert_eq!( v.get_block(1), 0b00000000 );

        v.set_block(0, 0b10101010 );
        assert_eq!( v.get_block(0), 0b10101010 );
        assert_eq!( v.get_block(1), 0b00000000 );

        v.set_block(1, 0b01010101 );
        assert_eq!( v.get_block(0), 0b10101010 );
        assert_eq!( v.get_block(1), 0b01010101 );

        assert_eq!( v.get_bit(0), false );
        assert_eq!( v.get_bit(1), true );
        assert_eq!( v.get_bit(2), false );
        assert_eq!( v.get_bit(3), true );
    }

    #[test]
    fn set_block_slice() {
        let mut v = vec![ false; 24 ];

        v.as_mut_slice().bit_slice(2..22).set_block(0, 0b11111111);
        assert_eq!( v.get_block(0), 0b11111100 );
        assert_eq!( v.get_block(1), 0b00000011 );
        assert_eq!( v.get_block(2), 0b00000000 );

        v.as_mut_slice().bit_slice(2..22).set_block(1, 0b11111111);
        assert_eq!( v.get_block(0), 0b11111100 );
        assert_eq!( v.get_block(1), 0b11111111 );
        assert_eq!( v.get_block(2), 0b00000011 );

        v.as_mut_slice().bit_slice(2..22).set_block(2, 0b11111111);
        assert_eq!( v.get_block(0), 0b11111100 );
        assert_eq!( v.get_block(1), 0b11111111 );
        assert_eq!( v.get_block(2), 0b00111111 );
    }
}
