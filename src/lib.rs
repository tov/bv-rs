extern crate num_traits;

#[cfg(test)]
extern crate quickcheck;

mod storage;
pub use self::storage::BlockType;

mod traits;
pub use self::traits::{BitVec, BitVecMut, BitVecPush, BitSliceable};

mod slice;
pub use self::slice::{BitSlice, BitSliceMut, BitSliceBlockIter};

mod bv;
pub use self::bv::BV;

mod prims;

