//! The main type exported by the library, [`BV`](struct.BV.html), is a packed,
//! growable bit-vector. Its API mirrors that of `Vec` where reasonable. The
//! library also defines slice operations that return
//! [`BitSlice`](struct.BitSlice.html) or [`BitSliceMut`](struct.BitSliceMut.html),
//! akin to Rust’s array slices but for bit-vectors. A common API to
//! bit-vectors and bit-slices is provided by the [`BitVec`](trait.BitVec.html),
//! [`BitVecMut`](trait.BitVecMut.html), and [`BitVecPush`](trait.BitVecPush.html)
//! traits, which also allow treating all primitive unsigned integer types
//! (`uN`), and vectors and slices thereof, as well as vectors and
//! slices of `bool`, as bit-vectors.
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

