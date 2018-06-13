# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog] and this project adheres to
[Semantic Versioning].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: http://semver.org/spec/v2.0.0.html

## [Unreleased]

### Added
- `adapter::BitsExt` trait, for adapter operations over types that implement `Bits`.
  Adapters include:
   - bit-wise logic adapters `BitNot`, `BitAnd`, `BitOr`, and `BitXor`;
   - `BitFill`;
   - `BitConcat`; and
   - `BitSliceAdapter`. (Note that `BitSliceAdapter` does not replace the more specialized 
     `BitSlice`.)
- `Bits::to_bit_vec` method, which copies the bits into a new `BitVec`.
- `bit_vec!` macro allows trailing comma.
  
### Removed
- `Bits::bit_offset` method. Blocks returned from a `Bits` instance are now
  assumed to be aligned.

## [0.7.2] - 2018-05-16

### Added
- A good number of doc examples.
- `html_doc_root` for cross-linking of docs.

## [0.7.1] - 2018-05-13

### Fixed
- Documentation, in many places.

## [0.7.0] - 2018-05-13

### Changed
- Renamed about half the types in the library. Doing this while it
  has no users! Changes are:
   - structures `BitVec{,Mut,Push}` -> `Bits{,Mut,Push}`
   - structure `Bv` -> `BitVec`
   - module `bv` -> `bit_vec`
   - macro `bv!` -> `bit_vec!`

## [0.6.6] - 2018-05-12

### Added
- Support for inclusive ranges.

## [0.6.4] - 2018-05-12

### Added
- Optional `serde` support, via Cargo feature `"serde"`.

### Removed
- Cargo feature `"u128"`, as `u128` support is now detected.

## [0.6.0] - 2018-05-11

### Changed
- Support for `u128` is now detected.
- No longer depends on `num-traits` crate.

## [0.5.0] - 2018-05-11

### Added
- Support for `u128`, enabled by Cargo feature `"u128"`.
- Version support statement: rustc 1.20.0.

## [0.4.4] - 2018-05-10

### Fixed
- Documentation URL.
- Version number in example toml.

## [0.4.3] - 2018-03-31

### Added
- Impl of `Default` for `BV`.
- Methods `BitSlice::is_empty` and `BitSliceMut::is_empty`.

## [0.4.2] - 2018-03-30

### Added
- Lots of tests.

### Fixed
- Added a necessary lifetime parameter.

## [0.4.1] - 2018-03-30

### Fixed
- `BV::align_block` and `BV::resize`.

## [0.4.0] - 2018-03-30

### Added
- Impl `BitSliceable` for `[bool]` and `Vec<bool>`.

### Changed
- Renamed method `BitSliceable::slice` to `BitSliceable::bit_slice`.

## [0.3.1] - 2018-03-30

### Added
- More tests.

### Fixed
- Bug in `block_len` method.

## [0.3.0] - 2018-03-28

### Added
- `bv!` macro.
- `BitSlice::len` and `BitSliceMut::len` methods.
- `BV::resize` method.

## [0.2.0] - 2018-03-28

### Added
- impl `BitVec` and `BitVecMut` for `[bool]`.

### Fixed
- Documentation.

## [0.1.2] - 2018-03-28

### Added
- Better crate summary in README.
- Documentation on bit slice representation.

## [0.1.1] - 2018-03-28

### Fixed
- Crate metadata.

## [0.1.0] - 2018-03-28

Initial release.
