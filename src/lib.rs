#![doc(html_root_url = "https://tov.github.io/bv-rs")]
//! The main type exported by the library, [`BitVec`](struct.BitVec.html), is a packed,
//! growable bit-vector. Its API mirrors that of `Vec` where reasonable. The
//! library also defines slice operations that return
//! [`BitSlice`](struct.BitSlice.html) or [`BitSliceMut`](struct.BitSliceMut.html),
//! akin to Rust’s array slices but for bit-vectors. A common API to
//! bit-vectors and bit-slices is provided by the [`Bits`](trait.Bits.html),
//! [`BitsMut`](trait.BitsMut.html), and [`BitsPush`](trait.BitsPush.html)
//! traits, which also allow treating as bit-vectors all primitive unsigned
//! integer types (`uN`), and vectors and slices thereof, as well as unpacked
//! vectors and slices of `bool`.
//!
//! # Example
//!
//! ```
//! use bv::BitVec;
//!
//! let mut bv1: BitVec = BitVec::new_fill(false, 50);
//! let mut bv2: BitVec = BitVec::new_fill(false, 50);
//!
//! assert_eq!(bv1, bv2);
//!
//! bv1.set(49, true);
//! assert_ne!(bv1, bv2);
//!
//! assert_eq!(bv1.pop(), Some(true));
//! assert_eq!(bv2.pop(), Some(false));
//! assert_eq!(bv1, bv2);
//! ```
//!
//! # Usage
//!
//! It’s [on crates.io](https://crates.io/crates/bv), so you can add
//!
//! ```toml
//! [dependencies]
//! bv = "0.7.4"
//! ```
//!
//! to your `Cargo.toml` and
//!
//! ```rust
//! extern crate bv;
//! ```
//!
//! to your crate root.
//!
//! This crate supports Rust version 1.20 and newer.

#![warn(missing_docs)]

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

mod util;

#[macro_use]
mod macros;

mod storage;
pub use self::storage::BlockType;

mod traits;
pub use self::traits::{Bits, BitsMut, BitsPush, BitSliceable};

mod slice;
pub use self::slice::{BitSlice, BitSliceMut};

mod bit_vec;
pub use self::bit_vec::BitVec;

mod array;
mod iter;
mod prims;

pub mod adapter;
