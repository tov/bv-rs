//! The main type exported by the library, `BV`, is a packed, growable
//! bit-vector. Its API mirrors that of `Vec` where reasonable. The library
//! also defines slices operations that return `BitSlice` or `BitSliceMut`,
//! akin to Rust’s array slices but for bit-vectors. A common API to
//! bit-vectors and bit-slices is provided by the `BitVec` and `BitVecMut`
//! traits, which also allow treating all primitive unsigned integer types
//! (`uN`), vectors thereof (`Vec<uN>`), and `Vec<bool>` as bit-vectors.
//!
//! # Usage
//!
//! It’s [on crates.io](https://crates.io/crates/bv), so you can add
//!
//! ```toml
//! [dependencies]
//! bv = "*"
//! ```
//!
//! to your `Cargo.toml` and
//!
//! ```rust
//! extern crate bv;
//! ```
//!
//! to your crate root.

#![warn(missing_docs)]

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

