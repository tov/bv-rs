//! This module impls the `Bits`, `BitsMut` and `BitSliceable` traits
//! for fixed-sized arrays of `BlockType`s.

use {BitRange, BlockType, Bits, BitsMut, BitSliceable};

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

            impl<'a, Block: BlockType> BitSliceable for &'a [Block; $size] {
                type Slice = <&'a [Block] as BitSliceable>::Slice;

                fn bit_slice<R: BitRange>(self, range: R) -> Self::Slice {
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

            impl<'a> BitSliceable for &'a [bool; $size] {
                type Slice = <&'a [bool] as BitSliceable>::Slice;

                fn bit_slice<R: BitRange>(self, range: R) -> Self::Slice {
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
    32 64 128 256 512 1024 2048 4096
    8_192 16_384 32_768 65_536 131_072 262_144 524_288 1_048_576
}

