#![feature(test)]

extern crate bv;
extern crate test;

use bv::BitVec;
use bv::{Bits, BitsExt, BitsMut};

use test::Bencher;
use std::cmp;

const NBITS: usize = 3200;

#[bench]
fn vec_bool_loop(b: &mut Bencher) {
    fn or_vec_bool(v1: &[bool], v2: &[bool]) -> Vec<bool> {
        let len = cmp::min(v1.len(), v2.len());
        let mut result = Vec::with_capacity(len);

        for i in 0 .. len {
            result.push(v1[i] | v2[i]);
        }

        result
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| {
        or_vec_bool(&or_vec_bool(&v1, &v2), &v3)
    })
}

#[bench]
fn vec_bool_iter(b: &mut Bencher) {
    fn or_vec_bool(v1: &[bool], v2: &[bool]) -> Vec<bool> {
        v1.iter().zip(v2.iter())
            .map(|(&b1, &b2)| b1 | b2)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| {
        or_vec_bool(&or_vec_bool(&v1, &v2), &v3)
    })
}

#[bench]
fn vec_bool_loop_fused(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        let len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let mut result = Vec::with_capacity(len);

        for i in 0 .. len {
            result.push(v1[i] | v2[i] | v3[i]);
        }

        result
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| {
        or_vec_bool_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_bool_iter_fused(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        v1.iter().zip(v2.iter()).zip(v3.iter())
            .map(|((&b1, &b2), &b3)| b1 | b2 | b3)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| {
        or_vec_bool_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_bitwise(b: &mut Bencher) {
    fn or_vec_u32(v1: &[u32], v2: &[u32]) -> Vec<u32> {
        let block_len = cmp::min(v1.len(), v2.len());
        let mut result = vec![0; block_len];

        for i in 0 .. 32 * block_len as u64 {
            result.set_bit(i, v1.get_bit(i) | v2.get_bit(i));
        }

        result
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32(&or_vec_u32(&v1, &v2), &v3)
    })
}

#[bench]
fn vec_u32_bitwise_fused(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        let block_len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let mut result = vec![0; block_len];

        for i in 0 .. 32 * block_len as u64 {
            result.set_bit(i, v1.get_bit(i) | v2.get_bit(i) | v3.get_bit(i));
        }

        result
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_loop(b: &mut Bencher) {
    fn or_vec_u32(v1: &[u32], v2: &[u32]) -> Vec<u32> {
        let len = cmp::min(v1.len(), v2.len());
        let mut result = Vec::with_capacity(len);

        for i in 0 .. len {
            result.push(v1[i] | v2[i]);
        }

        result
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32(&or_vec_u32(&v1, &v2), &v3)
    })
}

#[bench]
fn vec_u32_loop_fused(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        let len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let mut result = Vec::with_capacity(len);

        for i in 0 .. len {
            result.push(v1[i] | v2[i] | v3[i]);
        }

        result
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_iter(b: &mut Bencher) {
    fn or_vec_u32(v1: &[u32], v2: &[u32]) -> Vec<u32> {
        v1.iter().zip(v2.iter())
            .map(|(&z1, &z2)| z1 | z2)
            .collect()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32(&or_vec_u32(&v1, &v2), &v3)
    })
}

#[bench]
fn vec_u32_iter_fused(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        v1.iter().zip(v2.iter()).zip(v3.iter())
            .map(|((&z1, &z2), &z3)| z1 | z2 | z3)
            .collect()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_adapter(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> BitVec<u32> {
        v1.into_bit_or(v2).into_bit_or(v3).to_bit_vec()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[inline(never)]
fn three_vec_bools() -> (Vec<bool>, Vec<bool>, Vec<bool>) {
    (make_vec_bool(), make_vec_bool(), make_vec_bool())
}

fn make_vec_bool() -> Vec<bool> {
    vec![false; NBITS]
}

#[inline(never)]
fn three_vec_u32s() -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    (make_vec_u32(), make_vec_u32(), make_vec_u32())
}

fn make_vec_u32() -> Vec<u32> {
    vec![0; NBITS / 32]
}
