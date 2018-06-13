// Random testing for bit vector adapters.

extern crate bv;

#[macro_use]
extern crate quickcheck;

use bv::*;
use bv::adapter::*;

use quickcheck::{Arbitrary, Gen};

#[derive(Clone, Debug)]
struct RefImpl(Vec<bool>);

impl Arbitrary for RefImpl {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        RefImpl(<Vec<bool>>::arbitrary(g))
    }

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new(self.0.shrink().map(RefImpl))
    }
}

impl RefImpl {
    fn from_bits<T: Bits>(bits: &T) -> Self {
        let mut result = RefImpl(Vec::with_capacity(bits.bit_len() as usize));
        for i in 0 .. bits.bit_len() {
            result.0.push(bits.get_bit(i));
        }
        result
    }

    fn to_bit_vec<Block: BlockType>(bits: &RefImpl) -> BitVec<Block> {
        let mut result = BitVec::with_capacity(bits.0.len() as u64);
        for i in 0 .. bits.0.len() {
            result.push(bits.0[i])
        }
        result
    }
}

#[derive(Clone, Debug)]
enum Program {
    Constant(RefImpl),
    Not(Box<Program>),
    And(Box<Program>, Box<Program>),
    Or(Box<Program>, Box<Program>),
    Xor(Box<Program>, Box<Program>),
    Concat(Box<Program>, Box<Program>),
    Slice(Box<Program>, u64, u64),
    Force(Box<Program>),
}
