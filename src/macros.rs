/// Like `vec!` but for `BitVec`.
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
}