use super::BitsMut;
use storage::{BlockType, Address};
use BitVec;

/// Read-only bit vector operations.
///
/// Minimal complete definition is:
///
///   - `bit_len` and
///   - `get_bit` or `get_block`, since each is defined in terms of the other.
///
/// Note that `get_block` in terms of `get_bit` is inefficient, and thus
/// you should implement `get_block` directly if possible.
pub trait Bits {
    /// The underlying block type used to store the bits of the vector.
    type Block: BlockType;

    /// The length of the slice in bits.
    fn bit_len(&self) -> u64;

    /// The length of the slice in blocks.
    fn block_len(&self) -> usize {
        Self::Block::ceil_div_nbits(self.bit_len())
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

        let address = Address::new::<Self::Block>(position);
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
            if bit_position + i < self.bit_len() && self.get_bit(bit_position + i) {
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

        let address = Address::new::<Self::Block>(start);
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

    /// Copies the bits into a new allocated [`BitVec`].
    ///
    /// [`BitVec`]: ../struct.BitVec.html
    fn to_bit_vec(&self) -> BitVec<Self::Block> {
        BitVec::from_bits(self)
    }
}

impl<'a, T: Bits + ?Sized> Bits for &'a T {
    type Block = T::Block;

    fn bit_len(&self) -> u64 {
        T::bit_len(*self)
    }

    fn block_len(&self) -> usize {
        T::block_len(*self)
    }

    fn get_bit(&self, position: u64) -> bool {
        T::get_bit(*self, position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        T::get_block(*self, position)
    }

    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        T::get_bits(*self, start, count)
    }
}

impl<'a, T: Bits + ?Sized> Bits for &'a mut T {
    type Block = T::Block;

    fn bit_len(&self) -> u64 {
        T::bit_len(*self)
    }

    fn block_len(&self) -> usize {
        T::block_len(*self)
    }

    fn get_bit(&self, position: u64) -> bool {
        T::get_bit(*self, position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        T::get_block(*self, position)
    }

    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        T::get_bits(*self, start, count)
    }
}

impl<Block: BlockType> Bits for Box<Bits<Block = Block>> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        (**self).bit_len()
    }

    fn block_len(&self) -> usize {
        (**self).block_len()
    }

    fn get_bit(&self, position: u64) -> bool {
        (**self).get_bit(position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        (**self).get_block(position)
    }

    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        (**self).get_bits(start, count)
    }
}

impl<Block: BlockType> Bits for Box<BitsMut<Block = Block>> {
    type Block = Block;

    fn bit_len(&self) -> u64 {
        (**self).bit_len()
    }

    fn block_len(&self) -> usize {
        (**self).block_len()
    }

    fn get_bit(&self, position: u64) -> bool {
        (**self).get_bit(position)
    }

    fn get_block(&self, position: usize) -> Self::Block {
        (**self).get_block(position)
    }

    fn get_bits(&self, start: u64, count: usize) -> Self::Block {
        (**self).get_bits(start, count)
    }
}

