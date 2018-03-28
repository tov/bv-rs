use std::marker::PhantomData;

/// A slice of a bit-vector. Akin to `&'a [bool]` but packed.
pub struct BitSlice<'a, Block> {
    bits:   *const Block,
    offset: usize,
    len:    usize,
    marker: PhantomData<&'a ()>,
}

/// A mutable slice of a bit-vector. Akin to `&'a [bool]` but packed.
pub struct BitSliceMut<'a, Block> {
    bits:   *mut Block,
    offset: usize,
    len:    usize,
    marker: PhantomData<&'a mut ()>,
}