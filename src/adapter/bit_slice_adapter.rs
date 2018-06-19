use {BitRange, Bits, BitsMut, BitSliceable, BlockType};
use iter::BlockIter;

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

    /// Creates a new slice adapter from the given bit vector like.
    ///
    /// Takes the range to to slice by.
    ///
    /// # Panics
    ///
    /// If the range is improper or out of bounds.
    pub fn from_range<R: BitRange>(bits: T, range: R) -> Self {
        let (start, len) = range.interpret_range(bits.bit_len())
            .expect("BitSliceAdapter::from_range");
        BitSliceAdapter { bits, start, len }
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
            impl<$($param)*> ::BitSliceable for $target {
                type Slice = ::adapter::BitSliceAdapter<Self>;

                fn bit_slice<R: $crate::BitRange>(self, range: R) -> Self::Slice {
                    $crate::adapter::BitSliceAdapter::from_range(self, range)
                }
            }
        )+
    };
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

impl_index_from_bits! {
    impl[T: Bits] Index<u64> for BitSliceAdapter<T>;
}

impl<T: Bits> BitSliceable for BitSliceAdapter<T> {
    type Slice = Self;

    fn bit_slice<R: BitRange>(self, range: R) -> Self::Slice {
        let (start, len) = range.interpret_range(self.bit_len())
            .expect("<BitSliceAdapter<T>>::bit_slice)");
        BitSliceAdapter {
            bits:  self.bits,
            start: self.start + start,
            len,
        }
    }
}

