#![feature(test)]

extern crate bv;
extern crate test;

use bv::{Bits, BitsMut, BitVec};
use test::Bencher;

const NBITS: u64 = 640;

#[bench]
fn bit_vec_read(b: &mut Bencher) {
    let bv: BitVec = BitVec::new_fill(true, NBITS);

    b.iter(|| {
        let mut result = false;

        for i in 0 .. bv.len() {
            result ^= bv[i];
        }

        result
    })
}

#[bench]
fn bit_vec_write(b: &mut Bencher) {
    let mut bv: BitVec = BitVec::new_fill(true, NBITS);

    #[inline(never)]
    fn get_bit() -> bool { false }

    b.iter(|| {
        for i in 0 .. bv.len() {
            bv.set_bit(i, get_bit());
        }
    })
}

#[bench]
fn bit_vec_read_write(b: &mut Bencher) {
    let mut bv: BitVec = BitVec::new_fill(true, NBITS);

    #[inline(never)]
    fn get_bit() -> bool { false }

    b.iter(|| {
        for i in 0 .. bv.len() {
            let bit = bv[i] ^ get_bit();
            bv.set_bit(i, bit);
        }
    })
}

#[bench]
fn slice_read(b: &mut Bencher) {
    let v = vec![0u64; NBITS as usize / 64];
    let slice = v.as_slice();

    b.iter(|| {
        let mut result = false;

        for i in 0 .. slice.bit_len() {
            result ^= slice.get_bit(i as u64);
        }

        result
    })
}

#[bench]
fn slice_write(b: &mut Bencher) {
    let mut v = vec![0u64; NBITS as usize / 64];
    let slice = v.as_mut_slice();

    #[inline(never)]
    fn get_bit() -> bool { false }

    b.iter(|| {
        for i in 0 .. slice.bit_len() {
            slice.set_bit(i as u64, get_bit());
        }
    })
}

#[bench]
fn slice_read_write(b: &mut Bencher) {
    let mut v = vec![0u64; NBITS as usize / 64];
    let slice = v.as_mut_slice();

    #[inline(never)]
    fn get_bit() -> bool { false }

    b.iter(|| {
        for i in 0 .. slice.bit_len() {
            let bit = slice.get_bit(i) ^ get_bit();
            slice.set_bit(i, bit);
        }
    })
}
