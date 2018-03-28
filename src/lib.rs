extern crate num_traits;

#[cfg(test)]
extern crate quickcheck;

mod storage;
pub use self::storage::BlockType;

mod traits;
pub use self::traits::{BitVec, BitVecMut, BitVecPush};

mod bit_slice;
pub use self::bit_slice::{BitSlice, BitSliceMut};

mod prims;

