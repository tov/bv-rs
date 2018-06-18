#![feature(test)]

extern crate bv;
extern crate test;

use bv::*;
use test::Bencher;

const NBLOCKS: usize = 300;

#[bench]
fn copy_slice_array(b: &mut Bencher) {
    let vec = vec![0, NBLOCKS];
    let slice = vec.as_slice();
    b.iter(|| slice.to_bit_vec());
}

#[bench]
fn copy_slice_bit_vec(b: &mut Bencher) {
    let vec: BitVec = bit_vec![false; usize::mul_nbits(NBLOCKS)];
    b.iter(|| vec.to_bit_vec());
}

#[bench]
fn copy_slice_bit_slice(b: &mut Bencher) {
    let vec: BitVec = bit_vec![false; usize::mul_nbits(NBLOCKS)];
    let slice = vec.bit_slice(..);
    b.iter(|| slice.to_bit_vec());
}
