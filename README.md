# bv-rs: bit-vectors and bit-slices for Rust

[![Build Status](https://travis-ci.org/tov/bv-rs.svg?branch=master)](https://travis-ci.org/tov/succinct-rs)
[![Crates.io](https://img.shields.io/crates/v/bv.svg?maxAge=2592000)](https://crates.io/crates/succinct)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache_2.0-blue.svg)](LICENSE-APACHE)

The main type exported by the library, `BV`, is a packed, growable
bit-vector. Its API mirrors that of `Vec` where reasonable. The library
also defines slices operations that return `BitSlice` or `BitSliceMut`,
akin to Rust’s array slices but for bit-vectors. A common API to
bit-vectors and bit-slices is provided by the `BitVec` and `BitVecMut`
traits, which also allow treating all primitive unsigned integer types
(`uN`), vectors thereof (`Vec<uN>`), and `Vec<bool>` as bit-vectors.

## Usage

It’s [on crates.io](https://crates.io/crates/bv), so you can add

```toml
[dependencies]
bv = "*"
```

to your `Cargo.toml` and

```rust
extern crate bv;
```

to your crate root.
