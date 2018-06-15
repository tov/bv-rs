use traits::*;
use BlockType;
#[cfg(inclusive_range)]
use util;

use std::ops::{Range, RangeFrom, RangeTo, RangeFull};
#[cfg(inclusive_range)]
use std::ops::{RangeInclusive, RangeToInclusive};

impl<Block: BlockType> Bits for [Block] {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        Block::mul_nbits(self.len())
    }

    fn block_len(&self) -> usize {
        self.len()
    }

    fn get_block(&self, position: usize) -> Block {
        self[position]
    }
}

impl<Block: BlockType> Bits for Vec<Block> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        <[Block]>::bit_len(&self)
    }

    fn block_len(&self) -> usize {
        <[Block]>::block_len(&self)
    }

    fn get_block(&self, position: usize) -> Block {
        <[Block]>::get_block(&self, position)
    }
}

impl<Block: BlockType> BitsMut for [Block] {
    fn set_block(&mut self, position: usize, value: Block) {
        self[position] = value;
    }
}

impl<Block: BlockType> BitsMut for Vec<Block> {
    fn set_block(&mut self, position: usize, value: Block) {
        <[Block]>::set_block(&mut *self, position, value);
    }
}

impl Bits for [bool] {
    type Block = u8; // This is bogus

    #[inline]
    fn bit_len(&self) -> u64 {
        self.len() as u64
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

impl<'a> BitSliceable<Range<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: Range<u64>) -> &'a [bool] {
        &self[range.start as usize .. range.end as usize]
    }
}

impl<'a> BitSliceable<Range<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: Range<u64>) -> &'a mut [bool] {
        &mut self[range.start as usize .. range.end as usize]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeInclusive<u64>) -> &'a [bool] {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("<&[bool]>::bit_slice: bad inclusive range");
        // Adding 1 means we could overflow a 32-bit `usize` here, but
        // we can't construct a RangeInclusive on stable without using
        // the `..=` token, which breaks older rustcs.
        &self[start as usize .. end as usize + 1]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeInclusive<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeInclusive<u64>) -> &'a mut [bool] {
        let (start, end) = util::get_inclusive_bounds(&range)
            .expect("<&mut [bool]>::bit_slice: bad inclusive range");
        &mut self[start as usize .. end as usize + 1]
    }
}

impl<'a> BitSliceable<RangeFrom<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeFrom<u64>) -> &'a [bool] {
        &self[range.start as usize ..]
    }
}

impl<'a> BitSliceable<RangeFrom<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeFrom<u64>) -> &'a mut [bool] {
        &mut self[range.start as usize ..]
    }
}

impl<'a> BitSliceable<RangeTo<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeTo<u64>) -> &'a [bool] {
        &self[.. range.end as usize]
    }
}

impl<'a> BitSliceable<RangeTo<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeTo<u64>) -> &'a mut [bool] {
        &mut self[.. range.end as usize]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<u64>> for &'a [bool] {
    type Slice = &'a [bool];

    fn bit_slice(self, range: RangeToInclusive<u64>) -> &'a [bool] {
        &self[RangeToInclusive { end: range.end as usize }]
    }
}

#[cfg(inclusive_range)]
impl<'a> BitSliceable<RangeToInclusive<u64>> for &'a mut [bool] {
    type Slice = &'a mut [bool];

    fn bit_slice(self, range: RangeToInclusive<u64>) -> &'a mut [bool] {
        &mut self[RangeToInclusive { end: range.end as usize }]
    }
}

macro_rules! impl_traits_for_array {
    (
        $( $size:tt )+
    ) => {
        $(
            impl<Block: BlockType> Bits for [Block; $size] {
                type Block = Block;

                fn bit_len(&self) -> u64 {
                    Block::mul_nbits(self.block_len())
                }

                fn block_len(&self) -> usize {
                    $size
                }

                fn get_block(&self, position: usize) -> Self::Block {
                    self[position]
                }
            }

            impl<Block: BlockType> BitsMut for [Block; $size] {
                fn set_block(&mut self, position: usize, value: Block) {
                    self[position] = value;
                }
            }

            impl<'a, R, Block: BlockType> BitSliceable<R> for &'a [Block; $size]
                where &'a [Block]: BitSliceable<R> {

                type Slice = <&'a [Block] as BitSliceable<R>>::Slice;

                fn bit_slice(self, range: R) -> Self::Slice {
                    (self as &'a [Block]).bit_slice(range)
                }
            }

            impl Bits for [bool; $size] {
                type Block = u8;

                fn bit_len(&self) -> u64 {
                    $size
                }

                fn get_bit(&self, position: u64) -> bool {
                    self[position as usize]
                }
            }

            impl BitsMut for [bool; $size] {
                fn set_bit(&mut self, position: u64, value: bool) {
                    self[position as usize] = value;
                }
            }

            impl<'a, R> BitSliceable<R> for &'a [bool; $size]
                where &'a [bool]: BitSliceable<R> {

                type Slice = <&'a [bool] as BitSliceable<R>>::Slice;

                fn bit_slice(self, range: R) -> Self::Slice {
                    (self as &'a [bool]).bit_slice(range)
                }
            }
        )+
    };
}

impl_traits_for_array! {
    0 1 2 3 4 5 6 7
    8 9 10 11 12 13 14 15
    16 17 18 19 20 21 22 23
    24 25 26 27 28 29 30 31
}

