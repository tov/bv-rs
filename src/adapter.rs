//! Lazy bit vector adapters, including bit-wise logic.
//!
//! This module defines an extension trait [`BitsExt`] that is implemented
//! for every type that implements [`Bits`]. The trait provides bit-wise
//! logical and other operations on bit-vector-likes.
//!
//! [`Bits`]: ../trait.Bits.html
//! [`BitsExt`]: trait.BitsExt.html

use {Bits, BitsMut, BitsPush, BitSliceable};
use BlockType;
use iter::BlockIter;
use util;

use std::cmp;

use std::marker::PhantomData;
use std::ops::{self, Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

/// An adapter that turns any implementation of `Bits` into a slice.
///
/// This is likely less efficient than [`BitSlice`].
///
/// [`BitSlice`]: ../struct.BitSlice.html
#[derive(Copy, Clone, Debug)]
pub struct BitSliceAdapter<T> {
    bits:  T,
    start: u64,
    len:   u64,
}

impl<T: Bits> BitSliceAdapter<T> {
    /// Creates a new slice adaptor from the given bit-vector-like.
    ///
    /// Takes the index of the start bit, and the length to slice.
    ///
    /// # Panics
    ///
    /// Out of bounds if `start + len > bits.bit_len()`.
    pub fn new(bits: T, start: u64, len: u64) -> Self {
        assert!( start + len <= bits.bit_len(),
                 "BitSliceAdapter::new: out of bounds");
        BitSliceAdapter { bits, start, len }
    }

    /// Reslices an existing slice adapter, by value.
    ///
    /// Takes the index of the start bit, relative to the indexing
    /// of the adapter.
    ///
    /// # Panics
    ///
    /// Out of bounds if `start + len > self.bit_len()`.
    fn reslice(self, start: u64, len: u64) -> Self {
        assert!( start + len <= self.bit_len(),
                 "BitSliceAdapter::reslice: out of bounds" );
        BitSliceAdapter {
            bits:  self.bits,
            start: self.start + start,
            len,
        }
    }

    /// Reslices an existing slice adapter, by reference.
    ///
    /// Takes the index of the start bit, relative to the indexing
    /// of the adapter.
    ///
    /// # Panics
    ///
    /// Out of bounds if `start + len > self.bit_len()`.
    fn reslice_ref(&self, start: u64, len: u64) -> BitSliceAdapter<&T> {
        assert!( start + len <= self.bit_len(),
                 "BitSliceAdapter::reslice: out of bounds" );
        BitSliceAdapter {
            bits:  &self.bits,
            start: self.start + start,
            len,
        }
    }
}

impl<T, U> PartialEq<U> for BitSliceAdapter<T>
    where T: Bits,
          U: Bits<Block = T::Block> {

    fn eq(&self, other: &U) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

macro_rules! impl_bit_sliceable_adapter {
    (
        $(
            impl[ $($param:tt)* ] BitSliceable for $target:ty ;
        )+
    ) => {
        $(
            impl<$($param)*> BitSliceable<Range<u64>> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, range: Range<u64>) -> Self::Slice {
                    assert!( range.start <= range.end,
                             format!("{}::slice: bad range", stringify!($target)) );
                    BitSliceAdapter::new(self, range.start, range.end - range.start)
                }
            }

            impl<$($param)*> BitSliceable<RangeFrom<u64>> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, range: RangeFrom<u64>) -> Self::Slice {
                    let len = self.bit_len();
                    self.bit_slice(range.start .. len)
                }
            }

            impl<$($param)*> BitSliceable<RangeTo<u64>> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, range: RangeTo<u64>) -> Self::Slice {
                    BitSliceAdapter::new(self, 0, range.end)
                }
            }

            impl<$($param)*> BitSliceable<RangeFull> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, _range: RangeFull) -> Self::Slice {
                    let len = self.bit_len();
                    BitSliceAdapter::new(self, 0, len)
                }
            }

            #[cfg(inclusive_range)]
            impl<$($param)*> BitSliceable<RangeInclusive<u64>> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, range: RangeInclusive<u64>) -> Self::Slice {
                    let (start, end) = util::get_inclusive_bounds(&range)
                        .expect("BitSliceable::bit_slice: bad inclusive range");
                    BitSliceAdapter::new(self, start, end - start + 1)
                }
            }

            #[cfg(inclusive_range)]
            impl<$($param)*> BitSliceable<RangeToInclusive<u64>> for $target {
                type Slice = BitSliceAdapter<Self>;

                fn bit_slice(self, range: RangeToInclusive<u64>) -> Self::Slice {
                    BitSliceAdapter::new(self, 0, range.end + 1)
                }
            }
        )+
    };
}

// For a slice starting at `start`, of length `len`, finds the parameters
// for extracting the `position`th block. The parameters are the bit position
// of the start of the block, and the number of bits in the block.
fn get_block_addr<Block: BlockType>(start: u64, len: u64, position: usize)
    -> (u64, usize) {

    let real_start = start + Block::mul_nbits(position);
    let block_size = Block::nbits() as u64;
    let real_len   = if real_start + block_size < start + len {
        block_size
    } else {
        (start + len - real_start)
    };

    (real_start, real_len as usize)
}

impl<T: Bits> Bits for BitSliceAdapter<T> {
    type Block = T::Block;

    fn bit_len(&self) -> u64 {
        self.len
    }

    fn get_bit(&self, position: u64) -> bool {
        assert!( position < self.bit_len(),
                 "BitSliceAdapter::get_bit: out of bounds" );
        self.bits.get_bit(self.start + position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        assert!( position < self.block_len(),
                 "BitSliceAdapter::get_block: out of bounds" );
        let (real_start, real_len) =
            get_block_addr::<T::Block>(self.start, self.len, position);
        self.bits.get_bits(real_start, real_len)
    }

    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        assert!( start + count as u64 <= self.bit_len(),
                 "BitSliceAdapter::get_bits: out of bounds" );
        self.bits.get_bits(self.start + start, count)
    }
}

impl<T: BitsMut> BitsMut for BitSliceAdapter<T> {
    fn set_bit(&mut self, position: u64, value: bool) {
        assert!( position < self.bit_len(),
                 "BitSliceAdapter::set_bit: out of bounds" );
        self.bits.set_bit(self.start + position, value);
    }

    fn set_block(&mut self, position: usize, value: Self::Block) {
        assert!( position < self.block_len(),
                 "BitSliceAdapter::get_block: out of bounds" );
        let (real_start, real_len) =
            get_block_addr::<T::Block>(self.start, self.len, position);
        self.bits.set_bits(real_start, real_len, value);
    }

    fn set_bits(&mut self, start: u64, count: usize, value: Self::Block) {
        assert!( start + count as u64 <= self.bit_len(),
                 "BitSliceAdapter::set_bits: out of bounds" );
        self.bits.set_bits(self.start + start, count, value);
    }
}

impl_index_from_bits! {
    impl[T: Bits] Index<u64> for BitSliceAdapter<T>;
}

impl<T: Bits> BitSliceable<Range<u64>> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, range: Range<u64>) -> Self::Slice {
        assert!( range.start <= range.end,
                 "BitSliceAdapter::bit_slice: bad range" );
        self.reslice(range.start, range.end - range.start)
    }
}

impl<T: Bits> BitSliceable<RangeTo<u64>> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, range: RangeTo<u64>) -> Self::Slice {
        self.reslice(0, range.end)
    }
}

impl<T: Bits> BitSliceable<RangeFrom<u64>> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self::Slice {
        let len = self.bit_len();
        assert!( range.start <= len,
                 "BitSliceAdapter::bit_slice: out of bounds" );
        self.reslice(range.start, len - range.start)
    }
}

impl<T: Bits> BitSliceable<RangeFull> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, _range: RangeFull) -> Self::Slice {
        self
    }
}

#[cfg(inclusive_range)]
impl<T: Bits> BitSliceable<RangeInclusive<u64>> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self::Slice {
        let (start, limit) = util::get_inclusive_bounds(&range)
            .expect("BitSliceAdapter::bit_slice: bad range");
        self.reslice(start, limit - start + 1)
    }
}

#[cfg(inclusive_range)]
impl<T: Bits> BitSliceable<RangeToInclusive<u64>> for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self::Slice {
        self.reslice(0, range.end + 1)
    }
}

impl<'a, T: Bits> BitSliceable<Range<u64>> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, range: Range<u64>) -> Self::Slice {
        assert!( range.start <= range.end,
                 "BitSliceAdapter::bit_slice: bad range" );
        self.reslice_ref(range.start, range.end - range.start)
    }
}

impl<'a, T: Bits> BitSliceable<RangeTo<u64>> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, range: RangeTo<u64>) -> Self::Slice {
        self.reslice_ref(0, range.end)
    }
}

impl<'a, T: Bits> BitSliceable<RangeFrom<u64>> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, range: RangeFrom<u64>) -> Self::Slice {
        let len = self.bit_len();
        assert!( range.start <= len,
                 "BitSliceAdapter::bit_slice: out of bounds" );
        self.reslice_ref(range.start, len - range.start)
    }
}

impl<'a, T: Bits> BitSliceable<RangeFull> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, _range: RangeFull) -> Self::Slice {
        self.reslice_ref(0, self.bit_len())
    }
}

#[cfg(inclusive_range)]
impl<'a, T: Bits> BitSliceable<RangeInclusive<u64>> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, range: RangeInclusive<u64>) -> Self::Slice {
        let (start, limit) = util::get_inclusive_bounds(&range)
            .expect("BitSliceAdapter::bit_slice: bad range");
        self.reslice_ref(start, limit - start + 1)
    }
}

#[cfg(inclusive_range)]
impl<'a, T: Bits> BitSliceable<RangeToInclusive<u64>> for &'a BitSliceAdapter<T> {
    type Slice = BitSliceAdapter<&'a T>;

    fn bit_slice(self, range: RangeToInclusive<u64>) -> Self::Slice {
        self.reslice_ref(0, range.end + 1)
    }
}

/// Extension trait for adapter operations on bit slices.
///
/// The methods return lazy adapter objects that query the underlying bit vectors
/// and perform operations as needed. To eagerly evaluate a result, copy
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

impl_bit_sliceable_adapter! {
    impl['a, T: Bits] BitSliceable for &'a BitNot<T>;
}

impl<T, U> PartialEq<U> for BitNot<T>
    where T: Bits,
          U: Bits<Block = T::Block> {

    fn eq(&self, other: &U) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
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

        impl_bit_sliceable_adapter! {
            impl['a, T: Bits, U: Bits<Block = T::Block>] BitSliceable for &'a $target<T, U>;
        }

        impl<T, U, V> PartialEq<V> for $target<T, U>
            where T: Bits,
                  U: Bits<Block = T::Block>,
                  V: Bits<Block = T::Block> {

            fn eq(&self, other: &V) -> bool {
                BlockIter::new(self) == BlockIter::new(other)
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
        let limit_bit = cmp::min(start_bit + Self::Block::nbits() as u64,
                                 self.bit_len());

        let len0 = self.0.bit_len();
        if limit_bit <= len0 {
            self.0.get_block(position)
        } else if start_bit < len0 {
            let block1 = self.0.get_block(position);
            let block2 = self.1.get_block(0);
            let size1  = (len0 - start_bit) as usize;
            let size2  = Self::Block::nbits() - size1;
            block1.get_bits(0, size1) |
                (block2.get_bits(0, size2) << size1)
        } else {
            self.1.get_bits(start_bit - len0, (limit_bit - start_bit) as usize)
        }
    }
}

impl<T: Bits> PartialEq<T> for BitFill<T::Block> {
    fn eq(&self, other: &T) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

impl<T, U, V> PartialEq<V> for BitConcat<T, U>
    where T: Bits,
          U: Bits<Block = T::Block>,
          V: Bits<Block = T::Block> {

    fn eq(&self, other: &V) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

impl_index_from_bits! {
    impl[Block: BlockType] Index<u64> for BitFill<Block>;
    impl[T: Bits, U: Bits<Block = T::Block>] Index<u64> for BitConcat<T, U>;
}

impl_bit_sliceable_adapter! {
    impl[Block: BlockType] BitSliceable for BitFill<Block>;
    impl['a, Block: BlockType] BitSliceable for &'a BitFill<Block>;
    impl[T: Bits, U: Bits<Block = T::Block>] BitSliceable for BitConcat<T, U>;
    impl['a, T: Bits, U: Bits<Block = T::Block>] BitSliceable for &'a BitConcat<T, U>;
}

/// Adapts a sequence of `bool`s (*e.g.,* `&[bool]`) to emulate a bit
/// vector.
///
/// In particular, this adapter implements [`Bits`], [`BitsMut`], and
/// [`BitsPush`] as appropriate. It implement `PartialEq<T>` for all
/// `T: Bits<Block=Block>`. It does not, however, implement slicing, so
/// slice before you adapt.
///
/// Note that a bare `Vec<bool>` or `&[bool]` already implements [`Bits`],
/// etc., with a `Block` type of `u8`. This means that it is only
/// compatible with other `u8`-based bit vectors. `BoolAdapter` is instead
/// parametrized by the block type, so it works with bit vectors, slices,
/// and adapters of any uniform block type.
///
/// [`Bits`]: ../trait.Bits.html
/// [`BitsMut`]: ../trait.BitsMut.html
/// [`BitsPush`]: ../trait.BitsPush.html
#[derive(Debug, Clone)]
pub struct BoolAdapter<Block, T> {
    bits:    T,
    _marker: PhantomData<Block>,
}

impl<Block: BlockType, T> BoolAdapter<Block, T> {
    /// Creates a new `BoolAdapter` from an underlying sequence of `bool`s.
    ///
    /// Note that the `BoolAdapter` derefs to the underlying `bool` sequence.
    ///
    /// # Examples
    ///
    /// ```
    /// use bv::BitSliceable;
    /// use bv::adapter::BoolAdapter;
    ///
    /// let array = [0b101];
    /// let bv1 = BoolAdapter::<usize, _>::new(vec![true, false, true]);
    /// let bv2 = array.bit_slice(0..3);
    /// assert_eq!( bv1, bv2 );
    /// ```
    pub fn new(bits: T) -> Self {
        BoolAdapter {
            bits,
            _marker: PhantomData,
        }
    }

    /// Gets the underlying `bool` sequence object back out of a `BoolAdapter`.
    pub fn into_inner(self) -> T {
        self.bits
    }
}

impl<Block, T> ops::Deref for BoolAdapter<Block, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.bits
    }
}

impl<Block, T> ops::DerefMut for BoolAdapter<Block, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.bits
    }
}

macro_rules! impl_for_bool_adapter {
    () => {};

    (
        impl[$($param:tt)*] Bits for BoolAdapter<$block:ty, $target:ty>;
        $( $rest:tt )*
    ) => {
        impl<$($param)*> Bits for BoolAdapter<$block, $target> {
            type Block = $block;

            fn bit_len(&self) -> u64 {
                self.bits.len() as u64
            }

            fn get_bit(&self, position: u64) -> bool {
                self.bits[position as usize]
            }
        }

        impl_for_bool_adapter! { $($rest)* }
    };

    (
        impl[$($param:tt)*] BitsMut for BoolAdapter<$block:ty, $target:ty>;
        $( $rest:tt )*
    ) => {
        impl<$($param)*> BitsMut for BoolAdapter<$block, $target> {
            fn set_bit(&mut self, position: u64, value: bool) {
                self.bits[position as usize] = value
            }
        }

        impl_for_bool_adapter! { $($rest)* }
    };

    (
        impl[$($param:tt)*] BitsPush for BoolAdapter<$block:ty, $target:ty>;
        $( $rest:tt )*
    ) => {
        impl<$($param)*> BitsPush for BoolAdapter<$block, $target> {
            fn push_bit(&mut self, value: bool) {
                self.bits.push(value);
            }

            fn pop_bit(&mut self) -> Option<bool> {
                self.bits.pop()
            }
        }

        impl_for_bool_adapter! { $($rest)* }
    };
}

impl_for_bool_adapter! {
    impl[    Block: BlockType] Bits     for BoolAdapter<Block, Vec<bool>>;
    impl[    Block: BlockType] BitsMut  for BoolAdapter<Block, Vec<bool>>;
    impl[    Block: BlockType] BitsPush for BoolAdapter<Block, Vec<bool>>;

    impl['a, Block: BlockType] Bits     for BoolAdapter<Block, &'a mut Vec<bool>>;
    impl['a, Block: BlockType] BitsMut  for BoolAdapter<Block, &'a mut Vec<bool>>;
    impl['a, Block: BlockType] BitsPush for BoolAdapter<Block, &'a mut Vec<bool>>;

    impl['a, Block: BlockType] Bits     for BoolAdapter<Block, &'a mut [bool]>;
    impl['a, Block: BlockType] BitsMut  for BoolAdapter<Block, &'a mut [bool]>;

    impl['a, Block: BlockType] Bits     for BoolAdapter<Block, &'a [bool]>;
}

impl<Block, T, U> PartialEq<U> for BoolAdapter<Block, T>
    where Block: BlockType,
          U: Bits<Block = Block>,
          BoolAdapter<Block, T>: Bits<Block = Block> {

    fn eq(&self, other: &U) -> bool {
        BlockIter::new(self) == BlockIter::new(other)
    }
}

#[cfg(test)]
mod test {
    use {Bits, BitsMut, BitVec, BitSliceable};
    use super::{BitsExt, BitSliceAdapter};

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

    #[test]
    fn pad() {
        let bv1: BitVec = bit_vec![true, false, true, false];
        let bv2: BitVec = bit_vec![true, true];

        let bv3 = bv1.bit_or(bv2.bit_pad(bv1.bit_len())).to_bit_vec();

        assert_eq!( bv3, bit_vec![true, true, true, false] );
    }

    #[test]
    fn slice_adapter() {
        let bv1: BitVec = bit_vec![true, false, true, false, true, false, true, false];
        let bv2: BitVec = bit_vec![true, true, false, false, true, true, false, false];

        let bv3 = bv1.bit_xor(&bv2).bit_slice(1..7).to_bit_vec();

        assert_eq!( bv3, bit_vec![true, true, false, false, true, true] );
    }

    #[test]
    fn slice_adapter_mutation() {
        let mut bv: BitVec = bit_vec![true, false, true, false];

        {
            let mut slice = BitSliceAdapter::new(&mut bv, 1, 2);
            slice.set_bit(1, false);
        }

        assert_eq!( bv, bit_vec![true, false, false, false] );

        {
            let mut slice = BitSliceAdapter::new(&mut bv, 1, 2);
            slice.set_block(0, 0b111);
        }

        assert_eq!( bv, bit_vec![true, true, true, false] );
    }

    #[test]
    fn mixed_equality() {
        let bv1: BitVec = bit_vec![false, false, true, true];
        let bv2: BitVec = bit_vec![false, true, false, true];
        assert_eq!( bv1.bit_xor(&bv2), bit_vec![false, true, true, false] );
    }
}
