use super::storage::*;

/// A bit-vector.
#[derive(Clone)]
pub struct BV<Block = usize> {
    bits:   Box<[Block]>,
    len:    u64,
}

