extern crate num_traits;

#[cfg(test)]
extern crate quickcheck;

mod storage;
pub use self::storage::BlockType;

mod traits;
pub use self::traits::{BitVec, BitVecMut, BitVecPush};

mod slice;
pub use self::slice::{Sliceable, BitSlice, BitSliceMut};

mod prims;

