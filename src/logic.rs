//! Lazy logical operators on bit slices.

use Bits;

trait BitsLogic: Bits {
    fn bits_not(self) -> BitsNot<Self> where Self: Sized {
        BitsNot(self)
    }

    fn bits_and<Other: Bits>(self, other: Other) -> BitsAnd<Self, Other>
        where Self: Sized {

        BitsAnd(self, other)
    }

    fn bits_or<Other: Bits>(self, other: Other)  -> BitsOr<Self, Other>
        where Self: Sized {

        BitsOr(self, other)
    }

    fn bits_xor<Other: Bits>(self, other: Other) -> BitsXor<Self, Other>
        where Self: Sized {

        BitsXor(self, other)
    }
}

/// The result of [`BitsLogic::bits_not`](trait.BitsLogic.html#method.bits_not),
/// which inverts the bits of a bit vector.
pub struct BitsNot<T>(T);

/// The result of [`BitsLogic::bits_and`](trait.BitsLogic.html#method.bits_and)
/// on types that implement `Bits`.
pub struct BitsAnd<T, U>(T, U);

/// The result of [`BitsLogic::bits_or`](trait.BitsLogic.html#method.bits_or)
/// on types that implement `Bits`.
pub struct BitsOr<T, U>(T, U);

/// The result of [`BitsLogic::bits_xor`](trait.BitsLogic.html#method.bits_xor)
/// on types that implement `Bits`.
pub struct BitsXor<T, U>(T, U);
