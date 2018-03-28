/// Like `vec!` but for `BV`.
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate bv;
/// use bv::*;
///
/// fn main() {
///     let mut bv1: BV = bv![ true; 3 ];
///     let     bv2: BV = bv![ true, false, true ];
///
///     assert_ne!(bv1, bv2);
///     bv1.set_bit(1, false);
///     assert_eq!(bv1, bv2);
/// }
/// ```
#[macro_export]
macro_rules! bv {
    ( $e:expr ; $n:expr ) => {
        $crate::BV::new_fill($e, $n)
    };

    ( $( $e:expr ),* ) => {
        {
            let mut result = $crate::BV::new();
            $(
                result.push($e);
            )*
            result
        }
    };
}