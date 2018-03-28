use super::storage::*;

/// A bit-vector.
#[derive(Clone)]
pub struct BV<Block = usize> {
    bits:   Box<[Block]>,
    len:    u64,
}

impl<Block: BlockType> BV<Block> {
    /// The capacity of the bit-vector in bits.
    pub fn capacity(&self) -> u64 {
        Block::mul_nbits(self.block_capacity())
    }

    /// The capacity of the bit-vector in blocks.
    pub fn block_capacity(&self) -> usize {
        self.bits.len()
    }
}
