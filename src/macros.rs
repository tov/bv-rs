/// Like `vec!` but for [`BitVec`](struct.BitVec.html).
///
/// The `bit_vec!` macro creates a `BitVec` literal. It takes two forms:
///
///   - A single `bool`, followed by a semicolon and number of times to repeat. This is
///     equivalent to a call to [`BitVec::new_fill`](struct.BitVec.html#method.new_fill).
///
///   - A sequence of comma-separated `bool`s; this creates a `BitVec` and pushes each `bool` in
///     turn.
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate bv;
/// use bv::*;
///
/// fn main() {
///     let mut bv1: BitVec = bit_vec![ true; 3 ];
///     let     bv2: BitVec = bit_vec![ true, false, true ];
///
///     assert_ne!(bv1, bv2);
///     bv1.set_bit(1, false);
///     assert_eq!(bv1, bv2);
/// }
/// ```
#[macro_export]
macro_rules! bit_vec {
    ( $e:expr ; $n:expr ) => {
        $crate::BitVec::new_fill($e, $n)
    };

    ( $( $e:expr ),* ) => {
        {
            let mut result = $crate::BitVec::new();
            $(
                result.push($e);
            )*
            result
        }
    };

    ( $( $e:expr, )* ) => {
        bit_vec![ $($e),* ]
    };
}

#[test]
fn bit_vec_macro_allows_trailing_comma() {
    let bv1: super::BitVec = bit_vec![true, false, true];
    let bv2: super::BitVec = bit_vec![true, false, true,];
    assert_eq!( bv1, bv2 );
}