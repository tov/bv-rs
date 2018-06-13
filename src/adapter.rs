//! Lazy bit vector adapters, including bit-wise logic.
//!
//! This module defines an extension trait [`BitsExt`] that is implemented
//! for every type that implements [`Bits`]. The trait provides bit-wise
//! logical operations on bit-vector-likes.
//!
//! [`Bits`]: ../trait.Bits.html
//! [`BitsExt`]: trait.BitsExt.html

use Bits;
use BitSliceable;
use BlockType;

use std::cmp;

/// Extension trait for bit-wise logical operators on bit slices.
///
/// The methods return lazy adapter objects that query the underlying bit vectors
/// and perform logic operations as needed. To eagerly evaluate a result, copy
/// it into a vector using the [`Bits::to_bit_vec`] method, as in the example below.
///
/// [`Bits::to_bit_vec`]: ../trait.Bits.html#method.to_bit_vec
///
/// # Examples
///
/// ```
/// use bv::*;
/// use bv::adapter::BitsExt;
///
/// let bv1: BitVec = bit_vec![false, false, true, true];
/// let bv2: BitVec = bit_vec![false, true, false, true];
///
/// let and_bv = bv1.bit_and(&bv2);
///
/// assert_eq!( and_bv[0], false );
/// assert_eq!( and_bv[1], false );
/// assert_eq!( and_bv[2], false );
/// assert_eq!( and_bv[3], true );
///
/// let bv3 = and_bv.to_bit_vec();
/// assert_eq!( bv3, bit_vec![false, false, false, true] );
/// ```
pub trait BitsExt: Bits {

    /// Concatenates two bit vectors, with the bits of `self` followed by the bits
    /// of `other`.
    fn bit_concat<Other>(&self, other: Other) -> BitConcat<&Self, Other>
        where Other: Bits<Block = Self::Block> {

        BitConcat(self, other)
    }

    /// Concatenates two bit vectors, with the bits of `self` followed by the bits
    /// of `other`.
    ///
    /// Consumes `self`.
    fn into_bit_concat<Other>(self, other: Other) -> BitConcat<Self, Other>
        where Self: Sized,
              Other: Bits<Block = Self::Block> {

        BitConcat(self, other)
    }

    /// Pads `self` with 0s on the right to reach at least `len` bits in length.
    ///
    /// If `self` is already long enough, the length is unchanged.
    fn bit_pad(&self, len: u64) -> BitConcat<&Self, BitFill<Self::Block>> {
        self.into_bit_pad(len)
    }

    /// Pads `self` with 0s on the right to reach at least `len` bits in length.
    ///
    /// If `self` is already long enough, the length is unchanged.
    ///
    /// Consumes `self`.
    fn into_bit_pad(self, len: u64) -> BitConcat<Self, BitFill<Self::Block>>
        where Self: Sized {

        let have = self.bit_len();
        let need = if len > have {len - have} else {0};
        self.into_bit_concat(BitFill::zeroes(need))
    }

    /// Returns an object that inverts the values of all the bits in `self`.
    fn bit_not(&self) -> BitNot<&Self> {
        BitNot(self)
    }

    /// Returns an object that inverts the values of all the bits in `self`.
    ///
    /// Consumes `self`.
    fn into_bit_not(self) -> BitNot<Self>
        where Self: Sized
    {
        BitNot(self)
    }

    /// Returns an object that lazily computes the bit-wise conjunction
    /// of two bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    fn bit_and<Other>(&self, other: Other) -> BitAnd<&Self, Other>
        where Other: Bits<Block = Self::Block> {

        BitAnd(BitsBinOp::new(self, other))
    }

    /// Returns an object that lazily computes the bit-wise conjunction
    /// of two bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    ///
    /// Consumes `self`.
    fn into_bit_and<Other>(self, other: Other) -> BitAnd<Self, Other>
        where Self: Sized,
              Other: Bits<Block = Self::Block> {
        BitAnd(BitsBinOp::new(self, other))
    }

    /// Returns an object that lazily computes the bit-wise disjunction
    /// of two bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    fn bit_or<Other>(&self, other: Other) -> BitOr<&Self, Other>
        where Other: Bits<Block = Self::Block> {

        BitOr(BitsBinOp::new(self, other))
    }

    /// Returns an object that lazily computes the bit-wise disjunction
    /// of two bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    ///
    /// Consumes `self`.
    fn into_bit_or<Other>(self, other: Other) -> BitOr<Self, Other>
        where Self: Sized,
              Other: Bits<Block = Self::Block> {

        BitOr(BitsBinOp::new(self, other))
    }

    /// Returns an object that lazily computes the bit-wise xor of two
    /// bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    fn bit_xor<Other>(&self, other: Other) -> BitXor<&Self, Other>
        where Other: Bits<Block = Self::Block> {

        BitXor(BitsBinOp::new(self, other))
    }

    /// Returns an object that lazily computes the bit-wise xor of two
    /// bit-vector-likes.
    ///
    /// If the lengths of the operands differ, the result will have be
    /// the minimum of the two.
    ///
    /// Consumes `self`.
    fn into_bit_xor<Other>(self, other: Other) -> BitXor<Self, Other>
        where Self: Sized,
              Other: Bits<Block = Self::Block> {

        BitXor(BitsBinOp::new(self, other))
    }
}

impl<T: Bits> BitsExt for T {}

/// The result of [`BitsExt::bit_not`](trait.BitsExt.html#method.bit_not).
///
/// The resulting bit vector adapter *not*s the bits of the underlying
/// bit-vector-like.
#[derive(Clone, Debug)]
pub struct BitNot<T>(T);

/// The result of [`BitsExt::bit_and`](trait.BitsExt.html#method.bit_and).
///
/// The resulting bit vector adapter *and*s the bits of the two underlying
/// bit-vector-likes.
#[derive(Clone, Debug)]
pub struct BitAnd<T, U>(BitsBinOp<T, U>);

/// The result of [`BitsExt::bit_or`](trait.BitsExt.html#method.bit_or).
///
/// The resulting bit vector adapter *or*s the bits of the two underlying
/// bit-vector-likes.
#[derive(Clone, Debug)]
pub struct BitOr<T, U>(BitsBinOp<T, U>);

/// The result of [`BitsExt::bit_xor`](trait.BitsExt.html#method.bit_xor).
///
/// The resulting bit vector adapter *xor*s the bits of the two underlying
/// bit-vector-likes.
#[derive(Clone, Debug)]
pub struct BitXor<T, U>(BitsBinOp<T, U>);

/// Used to store the two operands to a bitwise logical operation on
/// `Bits`es, along with the length of the result (min the length of
/// the operands). (Note that `len` is derivable from `op1` and `op2`,
/// but it probably makes sense to cache it.)
#[derive(Clone, Debug)]
struct BitsBinOp<T, U> {
    op1: T,
    op2: U,
    len: u64,
}

impl<T: Bits, U: Bits<Block = T::Block>> BitsBinOp<T, U> {
    fn new(op1: T, op2: U) -> Self {
        let len = cmp::min(op1.bit_len(), op2.bit_len());
        BitsBinOp { op1, op2, len, }
    }

    fn bit1(&self, position: u64) -> bool {
        self.op1.get_bit(position)
    }

    fn bit2(&self, position: u64) -> bool {
        self.op2.get_bit(position)
    }

    fn block1(&self, position: usize) -> T::Block {
        self.op1.get_block(position)
    }

    fn block2(&self, position: usize) -> T::Block {
        self.op2.get_block(position)
    }
}

impl<T: Bits> Bits for BitNot<T> {
    type Block = T::Block;

    fn bit_len(&self) -> u64 {
        self.0.bit_len()
    }

    fn get_bit(&self, position: u64) -> bool {
        !self.0.get_bit(position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        !self.0.get_block(position)
    }
}

impl_index_from_bits! {
    impl[T: Bits] Index<u64> for BitNot<T>;
}

impl<R, T> BitSliceable<R> for BitNot<T>
    where T: BitSliceable<R> {

    type Slice = BitNot<T::Slice>;

    fn bit_slice(self, range: R) -> Self::Slice {
        BitNot(self.0.bit_slice(range))
    }
}

macro_rules! impl_bits_bin_op {
    ( $target:ident as $block_op:tt $bool_op:tt ) => {
        impl<T, U> Bits for $target<T, U>
            where T: Bits,
                  U: Bits<Block = T::Block>
        {
            type Block = T::Block;

            fn bit_len(&self) -> u64 {
                self.0.len
            }

            fn get_bit(&self, position: u64) -> bool {
                self.0.bit1(position) $bool_op self.0.bit2(position)
            }

            fn get_block(&self, position: usize) -> Self::Block {
                self.0.block1(position) $block_op self.0.block2(position)
            }
        }

        impl_index_from_bits! {
            impl[T: Bits, U: Bits<Block = T::Block>] Index<u64> for $target<T, U>;
        }

        impl<R, T, U> BitSliceable<R> for $target<T, U>
            where R: Clone,
                  T: BitSliceable<R>,
                  U: BitSliceable<R>,
                  T::Slice: Bits,
                  U::Slice: Bits<Block = <T::Slice as Bits>::Block> {

            type Slice = $target<T::Slice, U::Slice>;

            fn bit_slice(self, range: R) -> Self::Slice {
                $target(BitsBinOp::new(self.0.op1.bit_slice(range.clone()),
                                       self.0.op2.bit_slice(range)))
            }
        }
    };
}

impl_bits_bin_op!(BitAnd as & &&);
impl_bits_bin_op!(BitOr  as | ||);
impl_bits_bin_op!(BitXor as ^ ^);

/// Emulates a constant-valued bit-vector of a given size.
#[derive(Debug, Clone)]
pub struct BitFill<Block> {
    len: u64,
    block: Block,
}

impl<Block: BlockType> Bits for BitFill<Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn get_bit(&self, position: u64) -> bool {
        assert!(position < self.len,
                "BitFill::get_bit: out of bounds");
        self.block != Block::zero()
    }

    fn get_block(&self, position: usize) -> Self::Block {
        assert!(position < self.block_len(),
                "BitFill::get_block: out of bounds");
        self.block
    }

    fn get_bits(&self, position: u64, len: usize) -> Self::Block {
        assert!(position + (len as u64) <= self.bit_len(),
                "BitFill::get_bits: out of bounds");
        self.block
    }
}

impl<Block: BlockType> BitFill<Block> {
    /// Constructs a compact bit-vector-like of `len` 0s.
    pub fn zeroes(len: u64) -> Self {
        BitFill {
            len,
            block: Block::zero(),
        }
    }

    /// Constructs a compact bit-vector-like of `len` 1s.
    pub fn ones(len: u64) -> Self {
        BitFill {
            len,
            block: !Block::zero(),
        }
    }
}

/// The result of
/// [`BitsExt::bit_concat`](trait.BitsExt.html#method.bit_concat).
///
/// The resulting bit vector adapter concatenates the bits of the two underlying
/// bit-vector-likes.
#[derive(Debug, Clone)]
pub struct BitConcat<T, U>(T, U);

impl<T, U> Bits for BitConcat<T, U>
    where T: Bits,
          U: Bits<Block = T::Block> {

    type Block = T::Block;

    fn bit_len(&self) -> u64 {
        self.0.bit_len() + self.1.bit_len()
    }

    fn get_bit(&self, position: u64) -> bool {
        let len0 = self.0.bit_len();
        if position < len0 {
            self.0.get_bit(position)
        } else {
            self.1.get_bit(position - len0)
        }
    }

    fn get_block(&self, position: usize) -> Self::Block {
        let start_bit = Self::Block::mul_nbits(position);
        let end_bit   = cmp::min(start_bit + Self::Block::nbits() as u64,
                                 self.bit_len());

        let len0 = self.0.bit_len();
        if end_bit < len0 {
            self.0.get_block(position)
        } else if start_bit < len0 {
            let chunk1 = self.0.get_block(position);
            let chunk2 = self.1.get_block(0);
            let from1  = (len0 - start_bit) as usize;
            let from2  = Self::Block::nbits() - from1;
            chunk1.get_bits(0, from1) |
                (chunk2.get_bits(0, from2) << from1)
        } else {
            self.1.get_bits(start_bit - len0, (end_bit - start_bit) as usize)
        }
    }
}

impl_index_from_bits! {
    impl[Block: BlockType] Index<u64> for BitFill<Block>;
    impl[T: Bits, U: Bits<Block = T::Block>] Index<u64> for BitConcat<T, U>;
}

#[cfg(test)]
mod test {
    use {Bits, BitVec, BitSliceable};
    use super::BitsExt;

    fn assert_0001<T: Bits>(bits: &T) {
        assert_eq!( bits.bit_len(), 4 );

        assert!( !bits.get_bit(0) );
        assert!( !bits.get_bit(1) );
        assert!( !bits.get_bit(2) );
        assert!(  bits.get_bit(3) );

        let bv = bits.to_bit_vec();
        assert_eq!( bv, bit_vec![false, false, false, true] );
    }

    #[test]
    fn simple_not() {
        let bv: BitVec = bit_vec![true, true, true, false,];
        let not_bits = bv.bit_not();
        assert_0001(&not_bits);
    }

    #[test]
    fn simple_and() {
        let bv1: BitVec<u8> = bit_vec![ false, false, true, true, ];
        let bv2: BitVec<u8> = bit_vec![ false, true, false, true, ];
        let and_bits = bv1.bit_and(&bv2);
        assert_0001(&and_bits);
    }

    #[test]
    fn and_with_same_offset() {
        let bv1: BitVec<u8> = bit_vec![ true, false, false, true, true ];
        let bv2: BitVec<u8> = bit_vec![ true, false, true, false, true ];
        let bv_slice1 = bv1.bit_slice(1..);
        let bv_slice2 = bv2.bit_slice(1..);
        let and_bits = bv_slice1.bit_and(&bv_slice2);
        assert_0001(&and_bits);
    }

    #[test]
    fn and_with_different_offset() {
        let bv1: BitVec<u8> = bit_vec![ true, true, false, false, true, true ];
        let bv2: BitVec<u8> = bit_vec![ true, false, true, false, true ];
        let bv_slice1 = bv1.bit_slice(2..);
        let bv_slice2 = bv2.bit_slice(1..);
        let and_bits = bv_slice1.bit_and(&bv_slice2);
        assert_0001(&and_bits);
    }

    #[test]
    fn append() {
        let bv1: BitVec<u8> = bit_vec![false];
        let bv2: BitVec<u8> = bit_vec![true, true];
        let bv3: BitVec<u8> = bit_vec![false, false, false];

        let bv123 = bv1.bit_concat(&bv2).into_bit_concat(&bv3);
        let app12 = bv123.bit_concat(&bv123);
        let app24 = app12.bit_concat(&app12);
        let bv = BitVec::from_bits(&app24);

        assert_eq!(bv, bit_vec![false, true, true, false, false, false,
                                false, true, true, false, false, false,
                                false, true, true, false, false, false,
                                false, true, true, false, false, false]);
    }
}
