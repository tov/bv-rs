# bv-rs: bit-vectors and bit-slices for Rust

[![Build Status](https://travis-ci.org/tov/bv-rs.svg?branch=master)](https://travis-ci.org/tov/bv-rs)
[![Crates.io](https://img.shields.io/crates/v/bv.svg?maxAge=2592000)](https://crates.io/crates/bv)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache_2.0-blue.svg)](LICENSE-APACHE)

The main type exported by the library, `BV`, is a packed, growable
bit-vector. Its API mirrors that of `Vec` where reasonable. The library
also defines slice operations that return `BitSlice` or `BitSliceMut`,
akin to Rust’s array slices but for bit-vectors. A common API to
bit-vectors and bit-slices is provided by the `BitVec` and `BitVecMut`
traits, which also allow treating all primitive unsigned integer types
(`uN`) and vectors and array slices of the same primitive types as well
as of bool (`Vec<uN>`, `&[uN]`, `&mut [uN]`, `Vec<bool>`, `&[bool]`, and
`&mut [bool]`) as bit-vectors.

## Usage

It’s [on crates.io](https://crates.io/crates/bv), so you can add

```toml
[dependencies]
bv = "0.6"
```

to your `Cargo.toml` and

```rust
extern crate bv;
```

to your crate root.

This crate supports Rust version 1.20 and newer.
