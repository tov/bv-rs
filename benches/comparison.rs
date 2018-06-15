#![feature(test)]

extern crate bv;
extern crate test;

use bv::BitVec;
use bv::{Bits, BitsExt, BitsMut};

use test::Bencher;
use std::cmp;

const NBITS: usize = 9600;

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

    b.iter(|| or_vec_bool(&or_vec_bool(&v1, &v2), &v3));
}

#[bench]
fn vec_bool_loop_sliced(b: &mut Bencher) {
    fn or_vec_bool(v1: &[bool], v2: &[bool]) -> Vec<bool> {
        let len = cmp::min(v1.len(), v2.len());
        let s1  = &v1[..len];
        let s2  = &v2[..len];
        let mut result = s1.to_vec();

        {
            let sr = &mut result[..len];
            for i in 0 .. len {
                sr[i] |= s2[i];
            }
        }

        result
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| or_vec_bool(&or_vec_bool(&v1, &v2), &v3));
}

#[bench]
fn vec_bool_iter(b: &mut Bencher) {
    fn or_vec_bool(v1: &[bool], v2: &[bool]) -> Vec<bool> {
        v1.iter().cloned().zip(v2.iter().cloned())
            .map(|(b1, b2)| b1 | b2)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| or_vec_bool(&or_vec_bool(&v1, &v2), &v3));
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

    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
}

#[bench]
fn vec_bool_loop_fused_sliced(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        let len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let s1 = &v1[.. len];
        let s2 = &v2[.. len];
        let s3 = &v3[.. len];
        let mut result = vec![false; len];

        {
            let sr = &mut result[.. len];
            for i in 0 .. len {
                sr[i] = s1[i] | s2[i] | s3[i];
            }
        }

        result
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
}

#[bench]
fn vec_bool_loop_fused_sliced_or_assign(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        let len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let s1 = &v1[.. len];
        let s2 = &v2[.. len];
        let s3 = &v3[.. len];
        let mut result = s1.to_vec();

        {
            let sr = &mut result[.. len];
            for i in 0 .. len {
                sr[i] |= s2[i] | s3[i];
            }
        }

        result
    }

    let (v1, v2, v3) = three_vec_bools();

    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
}

#[bench]
fn vec_bool_iter_fused(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        v1.iter().zip(v2.iter()).zip(v3.iter())
            .map(|((b1, b2), b3)| *b1 | *b2 | *b3)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();
    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
}

#[bench]
fn vec_bool_iter_fused_cloned(b: &mut Bencher) {
    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        v1.iter().cloned().zip(v2.iter().cloned()).zip(v3.iter().cloned())
            .map(|((b1, b2), b3)| b1 | b2 | b3)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();
    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
}

#[bench]
fn vec_bool_iter_fused_bool_to_int(b: &mut Bencher) {
    fn bool_to_int(b: &bool) -> u32 {
        if *b {1} else {0}
    }

    fn or_vec_bool_3(v1: &[bool], v2: &[bool], v3: &[bool]) -> Vec<bool> {
        v1.iter().map(bool_to_int).zip(v2.iter().map(bool_to_int)).zip(v3.iter().map(bool_to_int))
            .map(|((b1, b2), b3)| b1 | b2 | b3 != 0)
            .collect()
    }

    let (v1, v2, v3) = three_vec_bools();
    b.iter(|| or_vec_bool_3(&v1, &v2, &v3));
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
fn vec_u32_loop_sliced(b: &mut Bencher) {
    fn or_vec_u32(v1: &[u32], v2: &[u32]) -> Vec<u32> {
        let len = cmp::min(v1.len(), v2.len());
        let s1 = &v1[.. len];
        let s2 = &v2[.. len];
        let mut result = s1.to_vec();

        {
            let sr = &mut result[.. len];
            for i in 0 .. len {
                sr[i] |= s2[i];
            }
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
fn vec_u32_loop_fused_assert(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        let len = v1.len();
        let mut result = v1.to_vec();
        assert_eq!( len, v2.len() );
        assert_eq!( len, v3.len() );
        assert_eq!( len, result.len() );

        for i in 0 .. len {
            result[i] |= v2[i] | v3[i];
        }

        result
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_loop_fused_assert_push(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        let len = v1.len();
        let mut result = Vec::with_capacity(len);
        assert_eq!( len, v1.len() );
        assert_eq!( len, v2.len() );
        assert_eq!( len, v3.len() );
        assert_eq!( len, result.capacity() );

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
fn vec_u32_loop_fused_sliced(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        let len = cmp::min(v1.len(), cmp::min(v2.len(), v3.len()));
        let s1 = &v1[.. len];
        let s2 = &v2[.. len];
        let s3 = &v3[.. len];
        let mut result = s1.to_vec();

        {
            let sr = &mut result[.. len];
            for i in 0 .. len {
                sr[i] |= s2[i] | s3[i];
            }
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
            .map(|(z1, z2)| *z1 | *z2)
            .collect()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32(&or_vec_u32(&v1, &v2), &v3)
    })
}
#[bench]
fn vec_u32_iter_cloned(b: &mut Bencher) {
    fn or_vec_u32(v1: &[u32], v2: &[u32]) -> Vec<u32> {
        v1.iter().cloned().zip(v2.iter().cloned())
            .map(|(z1, z2)| z1 | z2)
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
            .map(|((z1, z2), z3)| *z1 | *z2 | *z3)
            .collect()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[bench]
fn vec_u32_iter_fused_cloned(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> Vec<u32> {
        v1.iter().cloned().zip(v2.iter().cloned()).zip(v3.iter().cloned())
            .map(|((z1, z2), z3)| z1 | z2 | z3)
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

#[bench]
fn vec_u32_adapter_unfused(b: &mut Bencher) {
    fn or_vec_u32_3(v1: &[u32], v2: &[u32], v3: &[u32]) -> BitVec<u32> {
        v1.into_bit_or(v2).to_bit_vec().into_bit_or(v3).to_bit_vec()
    }

    let (v1, v2, v3) = three_vec_u32s();

    b.iter(|| {
        or_vec_u32_3(&v1, &v2, &v3)
    })
}

#[inline(never)]
fn three_vec_bools() -> (Vec<bool>, Vec<bool>, Vec<bool>) {
    let len = NBITS;
    (vec![false; len], vec![false; len], vec![false; len])
}

#[inline(never)]
fn three_vec_u32s() -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let len = NBITS / 32;
    (vec![0; len], vec![0; len], vec![0; len])
}
