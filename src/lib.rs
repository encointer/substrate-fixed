// Copyright © 2018 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

/*!
# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers. Currently it uses
the [*typenum* crate] for the fractional bit count; it is planned to
move to [const generics] when they are implemented by the Rust
compiler.

The crate provides the following types:

  * [`FixedI8`] is a signed eight-bit fixed-point number,
  * [`FixedI16`] is a signed 16-bit fixed-point number,
  * [`FixedI32`] is a signed 32-bit fixed-point number,
  * [`FixedI64`] is a signed 64-bit fixed-point number,
  * [`FixedI128`] is a signed 128-bit fixed-point number,
  * [`FixedU8`] is an unsigned eight-bit fixed-point number,
  * [`FixedU16`] is an unsigned 16-bit fixed-point number,
  * [`FixedU32`] is an unsigned 32-bit fixed-point number,
  * [`FixedU64`] is an unsigned 64-bit fixed-point number, and
  * [`FixedU128`] is an unsigned 128-bit fixed-point number.

All fixed-point numbers can have `Frac` fractional bits, where `Frac`
can have any value from 0 up to and including the size of the number
in bits. When `Frac` is 0, the fixed-point number behaves like an
integer. When `Frac` is equal to the number of bits, the value of the
fixed-point number lies in the range −0.5 ≤ *x* < 0.5 for signed
fixed-point numbers, and in the range 0 ≤ *x* < 1 for unsigned
fixed-point numbers.

## Quick example

```rust
use fixed::frac;
use fixed::FixedI32;

// 20 integer bits, 12 fractional bits
type I20F12 = FixedI32<frac::U12>;
// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19).unwrap() / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// convert to i32, taking the ceil
assert_eq!(six_and_third.to_int_ceil(), 7);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.1.3"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.28.0 or later.

## Optional features

The *fixed* crate has one optional feature:

 1. `f16`, disabled by default. This provides conversion to/from
    [`f16`]. This features requires the [*half* crate].

To enable the feature, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "0.1.3"
features = ["f16"]
```

## License

This crate is free software: you can redistribute it and/or modify it
under the terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache
License, Version 2.0, shall be dual licensed as above, without any
additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*fixed* crate]: https://crates.io/crates/fixed
[*half* crate]: https://crates.io/crates/half
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`FixedI128`]: struct.FixedI128.html
[`FixedI16`]: struct.FixedI16.html
[`FixedI32`]: struct.FixedI32.html
[`FixedI64`]: struct.FixedI64.html
[`FixedI8`]: struct.FixedI8.html
[`FixedU128`]: struct.FixedU128.html
[`FixedU16`]: struct.FixedU16.html
[`FixedU32`]: struct.FixedU32.html
[`FixedU64`]: struct.FixedU64.html
[`FixedU8`]: struct.FixedU8.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[channels]: https://doc.rust-lang.org/book/second-edition/appendix-07-nightly-rust.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.1.3")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(nightly_repr_transparent, feature(repr_transparent))]

#[cfg(feature = "f16")]
extern crate half;
extern crate typenum;

macro_rules! if_signed {
    (Signed => $($rem:tt)+) => {
        $($rem)+
    };
    (Unsigned => $($rem:tt)+) => {
    };
}
macro_rules! if_unsigned {
    (Signed => $($rem:tt)+) => {
    };
    (Unsigned => $($rem:tt)+) => {
        $($rem)+
    };
}

mod arith;
mod cmp;
mod display;
mod float;
pub mod frac;
mod helper;
mod wide_div;

use arith::MulDivDir;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use float::FloatConv;
use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
#[cfg(feature = "f16")]
use half::f16;
use helper::FixedHelper;

macro_rules! pass_method {
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident()) => {
        #[doc = $comment]
        #[inline]
        pub fn $method() -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method())
        }
    };
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident(self)) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self) -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method(self.to_bits()))
        }
    };
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident(self) -> $ret_ty:ty) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self) -> $ret_ty {
            <$Inner>::$method(self.to_bits())
        }
    };
    (
        $comment:expr,
        $Fixed:ident($Inner:ty) => fn $method:ident(self, $param:ident: $param_ty:ty)
    ) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self, $param: $param_ty) -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method(self.to_bits(), $param))
        }
    };
}

macro_rules! pass_method_signed_unsigned {
    ($Signedness:tt, $signed:expr, $unsigned:expr, $($tt:tt)*) => {
        if_signed! { $Signedness => pass_method! { $signed, $($tt)* } }
        if_unsigned! { $Signedness => pass_method! { $unsigned, $($tt)* } }
    }
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! doc_comment_signed_unsigned {
    ($Signedness:tt, $signed:expr, $unsigned:expr, $($tt:tt)*) => {
        if_signed! { $Signedness => doc_comment! { $signed, $($tt)* } }
        if_unsigned! { $Signedness => doc_comment! { $unsigned, $($tt)* } }
    };
}

macro_rules! from_float {
    ($Signedness:tt,fn $method:ident($Float:ident) -> $Fixed:ident < $Frac:ident >) => {
        doc_comment_signed_unsigned! {
            $Signedness,
            concat!(
                "Creates a fixed-point number from `", stringify!($Float), "`.\n",
                "\n",
                "This method rounds to the nearest, with ties rounding to even.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                "// 1.75 is 0001.1100, that is from_bits(28)\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(1.75), Some(Fix::from_bits(28)));\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(-1.75), Some(Fix::from_bits(-28)));\n",
                "// 1e-10 is too small for four fractional bits\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(1e-10), Some(Fix::from_bits(0)));\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(-1e-10), Some(Fix::from_bits(0)));\n",
                "// 2e38 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                "assert!(Fix::from_", stringify!($Float),
                "(2e38).is_none());\n",
                "assert!(Fix::from_", stringify!($Float),
                "(-2e38).is_none());\n",
                "```\n"
            ),
            concat!(
                "Creates a fixed-point number from `", stringify!($Float), "`.\n",
                "\n",
                "This method rounds to the nearest, with ties rounding to even.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                "// 1.75 is 0001.1100, that is from_bits(28)\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(1.75), Some(Fix::from_bits(28)));\n",
                "// 1e-10 is too small for four fractional bits\n",
                "assert_eq!(Fix::from_", stringify!($Float),
                "(1e-10), Some(Fix::from_bits(0)));\n",
                "// 2e38 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                "assert!(Fix::from_", stringify!($Float),
                "(2e38).is_none());\n",
                "```\n"
            ),
            #[inline]
            pub fn $method(val: $Float) -> Option<$Fixed<$Frac>> {
                let int_bits = Self::int_bits();
                let frac_bits = Self::frac_bits();

                let (int_frac, neg) = FloatConv::$method(val, frac_bits)?;

                if <$Fixed<$Frac> as FixedHelper<$Frac>>::is_signed() {
                    // most significant bit (msb) can be one only for min value,
                    // that is for a negative value with only the msb true.
                    let msb = 1 << (int_bits + frac_bits - 1);
                    if int_frac & msb != 0 {
                        if !neg || (int_frac & !msb) != 0 {
                            return None;
                        }
                    }
                } else if neg {
                    if int_frac != 0 {
                        return None;
                    }
                    return Some($Fixed::from_bits(0));
                }

                let (int, frac) = if frac_bits == 0 {
                    (int_frac, 0)
                } else if int_bits == 0 {
                    (0, int_frac)
                } else {
                    ((int_frac >> frac_bits), (int_frac << int_bits))
                };

                Some(FixedHelper::from_parts(neg, int, frac))
            }
        }
    };
}

macro_rules! to_float {
    ($Signedness:tt,fn $method:ident($Fixed:ident < $Frac:ident >) -> $Float:ident) => {
        doc_comment_signed_unsigned! {
            $Signedness,
            concat!(
                "Converts the fixed-point number to `", stringify!($Float), "`.\n",
                "\n",
                "This method rounds to the nearest, with ties rounding to even.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                "// 1.75 is 0001.1100, that is from_bits(28)\n",
                "assert_eq!(Fix::from_bits(28).to_", stringify!($Float),
                "(), 1.75);\n",
                "assert_eq!(Fix::from_bits(-28).to_", stringify!($Float),
                "(), -1.75);\n",
                "```\n"
            ),
            concat!(
                "Converts the fixed-point number to `", stringify!($Float), "`.\n",
                "\n",
                "This method rounds to the nearest, with ties rounding to even.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                "// 1.75 is 0001.1100, that is from_bits(28)\n",
                "assert_eq!(Fix::from_bits(28).to_", stringify!($Float),
                "(), 1.75);\n",
                "```\n"
            ),
            #[inline]
            pub fn $method(self) -> $Float {
                let int_bits = Self::int_bits();
                let frac_bits = Self::frac_bits();
                let (neg, int, frac) = self.parts();
                let int_frac = if frac_bits == 0 {
                    int
                } else if int_bits == 0 {
                    frac
                } else {
                    (int << frac_bits) | (frac >> int_bits)
                };
                FloatConv::$method(int_frac, neg, frac_bits)
            }
        }
    };
}

#[cfg(feature = "f16")]
macro_rules! string_up_to_16 {
    (U8, $s:expr) => {
        $s
    };
    (U16, $s:expr) => {
        $s
    };
    ($other:tt, $s:expr) => {
        ""
    };
}

macro_rules! fixed {
    ($description:expr, $Fixed:ident($Inner:ty, $Len:tt, $bits_count:expr), $Signedness:tt) => {
        doc_comment! {
            concat!(
                $description,
                "\nwith `Frac` fractional bits.\n",
                "\n",
                "Currently `Frac` is an [`Unsigned`] as provided by\n",
                "the [typenum crate]; it is planned to move to\n",
                "[const generics] when they are implemented by the\n",
                "Rust compiler.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac::U3;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "let eleven = ", stringify!($Fixed), "::<U3>::from_bits(11 << 3);\n",
                "let five_half = eleven >> 1u32;\n",
                "assert_eq!(eleven.to_string(), \"11.0\");\n",
                "assert_eq!(five_half.to_string(), \"5.5\");\n",
                "```\n",
                "\n",
                "[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html\n",
                "[const generics]: https://github.com/rust-lang/rust/issues/44580\n",
                "[typenum crate]: https://crates.io/crates/typenum\n"
            ),
            #[repr(transparent)]
            pub struct $Fixed<Frac>(($Inner, PhantomData<Frac>))
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>;
        }

        impl<Frac> Clone for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn clone(&self) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits())
            }
        }

        impl<Frac> Copy for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {}

        impl<Frac> Default for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn default() -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as Default>::default())
            }
        }

        impl<Frac> Hash for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn hash<H>(&self, state: &mut H)
            where
                H: Hasher,
            {
                self.to_bits().hash(state);
            }
        }

        impl<Frac> $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            pass_method_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the smallest value that can be represented.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "assert_eq!(Fix::min_value(), Fix::from_bits(",
                    stringify!($Inner), "::min_value()));\n",
                    "```\n"
                ),
                concat!(
                    "Returns the smallest value that can be represented.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "assert_eq!(Fix::min_value(), Fix::from_bits(0));\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn min_value()
            }
            pass_method! {
                concat!(
                    "Returns the smallest value that can be represented.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "assert_eq!(Fix::max_value(), Fix::from_bits(",
                    stringify!($Inner), "::max_value()));\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn max_value()
            }

            doc_comment! {
                concat!(
                    "Returns the number of integer bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U6>;\n",
                    "assert_eq!(Fix::int_bits(), ", stringify!($bits_count), " - 6);\n",
                    "```\n"
                ),
                #[inline]
                pub fn int_bits() -> u32 {
                    <Self as FixedHelper<Frac>>::int_frac_bits() - Self::frac_bits()
                }
            }

            doc_comment! {
                concat!(
                    "Returns the number of fractional bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U6>;\n",
                    "assert_eq!(Fix::frac_bits(), 6);\n",
                    "```\n"
                ),
                #[inline]
                pub fn frac_bits() -> u32 {
                    Frac::to_u32()
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number of type `", stringify!($Fixed), "`\n",
                    "that has a bitwise representation identical to the\n",
                    "`", stringify!($Inner), "` value.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000 == 2\n",
                    "assert_eq!(Fix::from_bits(0b10_0000), 2);\n",
                    "```\n"
                ),
                #[inline]
                pub fn from_bits(v: $Inner) -> $Fixed<Frac> {
                    $Fixed((v, PhantomData))
                }
            }

            doc_comment! {
                concat!(
                    "Creates an integer of type `", stringify!($Inner), "`\n",
                    "that has a bitwise representation identical to the\n",
                    "`", stringify!($Fixed), "` value.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two = Fix::from_int(2).unwrap();\n",
                    "// two is 0010.0000\n",
                    "assert_eq!(two.to_bits(), 0b10_0000);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_bits(self) -> $Inner {
                    (self.0).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number of type `", stringify!($Fixed), "`\n",
                    "that has the same value as an integer of type\n",
                    "`", stringify!($Inner), "` if it fits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let fix_one = Fix::from_bits(1 << 4);\n",
                    "assert_eq!(Fix::from_int(1), Some(fix_one));\n",
                    "let too_large = 1 << (", stringify!($bits_count), " - 2);\n",
                    "assert_eq!(Fix::from_int(too_large), None);\n",
                    "```\n"
                ),
                #[inline]
                pub fn from_int(v: $Inner) -> Option<$Fixed<Frac>> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let bits = v.checked_shl(frac_bits).unwrap_or(0);
                    let all_frac_check;
                    if_signed! { $Signedness => all_frac_check = bits >> (frac_bits - 1); }
                    if_unsigned! { $Signedness => all_frac_check = 0; }

                    let check = bits.checked_shr(frac_bits).unwrap_or(all_frac_check);
                    if check == v {
                        Some($Fixed::from_bits(bits))
                    } else {
                        None
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` truncating the fractional bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int(), 2);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int(), -2);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` truncating the fractional bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int(), 2);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int(self) -> $Inner {
                    let floor = self.to_int_floor();
                    if_signed! { $Signedness => {
                        let no_frac = self.frac().to_bits() == 0;
                        if no_frac || self.to_bits() >= 0 {
                            floor
                        } else {
                            floor + 1
                        }
                    } }
                    if_unsigned! { $Signedness => {
                        floor
                    } }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards +∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_ceil(), 3);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_ceil(), -2);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards +∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_ceil(), 3);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_ceil(self) -> $Inner {
                    let floor = self.to_int_floor();
                    let no_frac = self.frac().to_bits() == 0;
                    if no_frac {
                        floor
                    } else {
                        floor + 1
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_floor(), 2);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_floor(), -3);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_floor(), 2);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_floor(self) -> $Inner {
                    let bits = self.to_bits();
                    if Self::int_bits() == 0 {
                        if_signed! { $Signedness => bits >> (Self::frac_bits() - 1) }
                        if_unsigned! { $Signedness => 0 }
                    } else {
                        bits >> Self::frac_bits()
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards the nearest.\n",
                    "Ties are rounded away from zero.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_round(), 3);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_round(), -3);\n",
                    "let one_quarter = two_half / 2;\n",
                    "assert_eq!(one_quarter.to_int_round(), 1);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_round(), 3);\n",
                    "let one_quarter = two_half / 2;\n",
                    "assert_eq!(one_quarter.to_int_round(), 1);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_round(self) -> $Inner {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let floor = self.to_int_floor();
                    if frac_bits == 0 {
                        return floor;
                    }
                    let half_bit = 1 << (frac_bits - 1);
                    if_signed! { $Signedness => {
                        if self.to_bits() >= 0 {
                            if (self.to_bits() & half_bit) != 0 {
                                floor + 1
                            } else {
                                floor
                            }
                        } else {
                            let neg =  self.to_bits().wrapping_neg();
                            if (neg & half_bit) != 0 {
                                floor
                            } else {
                                floor + 1
                            }
                        }
                    } }
                    if_unsigned! { $Signedness => {
                        if (self.to_bits() & half_bit) != 0 {
                            floor + 1
                        } else {
                            floor
                        }
                    } }
                }
            }

            #[cfg(feature = "f16")]
            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Creates a fixed-point number from `f16`.\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "This method is only available when the `f16` feature is enabled.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "extern crate fixed;\n",
                    "extern crate half;\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use half::f16;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let val = f16::from_f32(1.75);\n",
                    "let neg_val = f16::from_f32(-1.75);\n",
                    "assert_eq!(Fix::from_f16(val), Some(Fix::from_bits(28)));\n",
                    "assert_eq!(Fix::from_f16(neg_val), Some(Fix::from_bits(-28)));\n",
                    "// 1e-2 is too small for four fractional bits\n",
                    "let small = f16::from_f32(1e-2);\n",
                    "let neg_small = f16::from_f32(-1e-2);\n",
                    "assert_eq!(Fix::from_f16(small), Some(Fix::from_bits(0)));\n",
                    "assert_eq!(Fix::from_f16(neg_small), Some(Fix::from_bits(0)));\n",
                    string_up_to_16!(
                        $Len,
                        concat!(
                            "// 50000 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                            "let large = f16::from_f32(50000.0);\n",
                            "let neg_large = f16::from_f32(-50000.0);\n",
                            "assert!(Fix::from_f16(large).is_none());\n",
                            "assert!(Fix::from_f16(neg_large).is_none());\n"
                        )
                    ),
                    "```\n"
                ),
                concat!(
                    "Creates a fixed-point number from `", stringify!($Float), "`.\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "This method is only available when the `f16` feature is enabled.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "extern crate fixed;\n",
                    "extern crate half;\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use half::f16;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let val = f16::from_f32(1.75);\n",
                    "assert_eq!(Fix::from_f16(val), Some(Fix::from_bits(28)));\n",
                    "// 1e-2 is too small for four fractional bits\n",
                    "let small = f16::from_f32(1e-2);\n",
                    "assert_eq!(Fix::from_f16(small), Some(Fix::from_bits(0)));\n",
                    string_up_to_16!(
                        $Len,
                        concat!(
                            "// 50000 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                            "let large = f16::from_f32(50000.0);\n",
                            "assert!(Fix::from_f16(large).is_none());\n",
                        )
                    ),
                    "```\n"
            ),
            #[inline]
                pub fn from_f16(val: f16) -> Option<$Fixed<Frac>> {
                    let int_bits = Self::int_bits();
                    let frac_bits = Self::frac_bits();

                    let (int_frac, neg) = FloatConv::from_f16(val, frac_bits)?;

                    if <$Fixed<Frac> as FixedHelper<Frac>>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb = 1 << (int_bits + frac_bits - 1);
                        if int_frac & msb != 0 {
                            if !neg || (int_frac & !msb) != 0 {
                                return None;
                            }
                        }
                    } else if neg {
                        if int_frac != 0 {
                            return None;
                        }
                        return Some($Fixed::from_bits(0));
                    }

                    let (int, frac) = if frac_bits == 0 {
                        (int_frac, 0)
                    } else if int_bits == 0 {
                        (0, int_frac)
                    } else {
                        ((int_frac >> frac_bits), (int_frac << int_bits))
                    };

                    Some(FixedHelper::from_parts(neg, int, frac))
                }
            }

            from_float! { $Signedness, fn from_f32(f32) -> $Fixed<Frac> }
            from_float! { $Signedness, fn from_f64(f64) -> $Fixed<Frac> }

            #[cfg(feature = "f16")]
            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number to `f16`.\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "This method is only available when the `f16` feature is enabled.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "extern crate fixed;\n",
                    "extern crate half;\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use half::f16;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let val = f16::from_f32(1.75);\n",
                    "let neg_val = f16::from_f32(-1.75);\n",
                    "assert_eq!(Fix::from_bits(28).to_f16(), val);\n",
                    "assert_eq!(Fix::from_bits(-28).to_f16(), neg_val);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number to `f16`.\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "This method is only available when the `f16` feature is enabled.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "extern crate fixed;\n",
                    "extern crate half;\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use half::f16;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let val = f16::from_f32(1.75);\n",
                    "assert_eq!(Fix::from_bits(28).to_f16(), val);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_f16(self) -> f16 {
                    let int_bits = Self::int_bits();
                    let frac_bits = Self::frac_bits();
                    let (neg, int, frac) = self.parts();
                    let int_frac = if frac_bits == 0 {
                        int
                    } else if int_bits == 0 {
                        frac
                    } else {
                        (int << frac_bits) | (frac >> int_bits)
                    };
                    FloatConv::to_f16(int_frac, neg, frac_bits)
                }
            }

            to_float! { $Signedness, fn to_f32($Fixed<Frac>) -> f32 }
            to_float! { $Signedness, fn to_f64($Fixed<Frac>) -> f64 }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the integer part.\n",
                    "\n",
                    "Note that since the numbers are stored in two’s\n",
                    "complement, negative numbers with non-zero fractional\n",
                    "parts will be rounded towards −∞, except in the case\n",
                    "where there are no integer bits, that is `",
                    stringify!($Fixed), "<U", stringify!($bits_count), ">`,\n",
                    "where the return value is always zero.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000\n",
                    "let two = Fix::from_int(2).unwrap();\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "// 1101.0000\n",
                    "let neg_three = Fix::from_int(-3).unwrap();\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.int(), neg_three);\n",
                    "```\n"
                ),
                concat!(
                    "Returns the integer part.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000\n",
                    "let two = Fix::from_int(2).unwrap();\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "```\n"
                ),
                #[inline]
                pub fn int(self) -> $Fixed<Frac> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let mask = <$Inner>::checked_shl(!0, frac_bits).unwrap_or(0);
                    $Fixed::from_bits(self.to_bits() & mask)
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the fractional part.\n",
                    "\n",
                    "Note that since the numbers are stored in two’s\n",
                    "complement, the returned fraction will be non-negative\n",
                    "for negative numbers, except in the case where\n",
                    "there are no integer bits, that is `",
                    stringify!($Fixed), "<U", stringify!($bits_count), ">`,\n",
                    "where the return value is always equal to `self`.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0000.0100\n",
                    "let quarter = Fix::from_int(1).unwrap() / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "// 0000.1100\n",
                    "let three_quarters = quarter * 3;\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.frac(), three_quarters);\n",
                    "```\n"
                ),
                concat!(
                    "Returns the fractional part.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0000.0100\n",
                    "let quarter = Fix::from_int(1).unwrap() / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "```\n"
                ),
                #[inline]
                pub fn frac(self) -> $Fixed<Frac> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let inv_mask = <$Inner>::checked_shl(!0, frac_bits).unwrap_or(0);
                    $Fixed::from_bits(self.to_bits() & !inv_mask)
                }
            }

            pass_method! {
                concat!(
                    "Returns the number of ones in the binary representation.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let f = Fix::from_bits(0b11_0010);\n",
                    "assert_eq!(f.count_ones(), 3);\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn count_ones(self) -> u32
            }
            pass_method! {
                concat!(
                    "Returns the number of zeros in the binary representation.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let f = Fix::from_bits(!0b11_0010);\n",
                    "assert_eq!(f.count_zeros(), 3);\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn count_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "Returns the number of leading zeros in the binary representation.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let f = Fix::from_bits(0b10_0000);\n",
                    "assert_eq!(f.leading_zeros(), ", stringify!($bits_count), " - 6);\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn leading_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "Returns the number of trailing zeros in the binary representation.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let f = Fix::from_bits(0b10_0000);\n",
                    "assert_eq!(f.trailing_zeros(), 5);\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn trailing_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "Shifts to the left by *n* bits, wrapping the truncated bits to the right end.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let bits: ", stringify!($Inner), " = (0b111 << (",
                    stringify!($bits_count), " - 3)) | 0b1010;\n",
                    "let rot = 0b1010111;\n",
                    "assert_eq!(bits.rotate_left(3), rot);\n",
                    "assert_eq!(Fix::from_bits(bits).rotate_left(3), Fix::from_bits(rot));\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn rotate_left(self, n: u32)
            }
            pass_method! {
                concat!(
                    "Shifts to the right by *n* bits, wrapping the truncated bits to the left end.",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let bits: ", stringify!($Inner), " = 0b1010111;\n",
                    "let rot = (0b111 << (",
                    stringify!($bits_count), " - 3)) | 0b1010;\n",
                    "assert_eq!(bits.rotate_right(3), rot);\n",
                    "assert_eq!(Fix::from_bits(bits).rotate_right(3), Fix::from_bits(rot));\n",
                    "```\n"
                ),
                $Fixed($Inner) => fn rotate_right(self, n: u32)
            }

            /// Checked negation.
            #[inline]
            pub fn checked_neg(self) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_neg(self.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point addition.
            #[inline]
            pub fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_add(self.to_bits(), rhs.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point subtraction.
            #[inline]
            pub fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_sub(self.to_bits(), rhs.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point multiplication.
            #[inline]
            pub fn checked_mul(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => Some($Fixed::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point division.
            #[inline]
            pub fn checked_div(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                if rhs.to_bits() == 0 {
                    return None;
                }
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => Some($Fixed::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point multiplication by integer.
            #[inline]
            pub fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_mul(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point division by integer.
            #[inline]
            pub fn checked_div_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_div(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point remainder for division by integer.
            #[inline]
            pub fn checked_rem_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_rem(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point left shift.
            #[inline]
            pub fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shl(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point right shift.
            #[inline]
            pub fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shr(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            if_signed! {
                $Signedness =>
                /// Checked absolute value.
                #[inline]
                pub fn checked_abs(self) -> Option<$Fixed<Frac>> {
                    <$Inner>::checked_abs(self.to_bits()).map($Fixed::from_bits)
                }
            }

            /// Saturating fixed-point addition.
            #[inline]
            pub fn saturating_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_add(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point subtraction.
            #[inline]
            pub fn saturating_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point multiplication.
            #[inline]
            pub fn saturating_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => $Fixed::from_bits(ans),
                    Ordering::Less => $Fixed::max_value(),
                    Ordering::Greater => $Fixed::min_value(),
                }
            }

            /// Saturating fixed-point division.
            #[inline]
            pub fn saturating_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => $Fixed::from_bits(ans),
                    Ordering::Less => $Fixed::max_value(),
                    Ordering::Greater => $Fixed::min_value(),
                }
            }

            /// Saturating fixed-point multiplication by integer.
            #[inline]
            pub fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_mul(self.to_bits(), rhs))
            }

            /// Wrapping negation.
            #[inline]
            pub fn wrapping_neg(self) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_neg(self.to_bits()))
            }

            /// Wrapping fixed-point addition.
            #[inline]
            pub fn wrapping_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_add(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point subtraction.
            #[inline]
            pub fn wrapping_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point multiplication.
            #[inline]
            pub fn wrapping_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                $Fixed::from_bits(ans)
            }

            /// Wrapping fixed-point division.
            #[inline]
            pub fn wrapping_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                $Fixed::from_bits(ans)
            }

            /// Wrapping fixed-point multiplication by integer.
            #[inline]
            pub fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_mul(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point division by integer.
            #[inline]
            pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_div(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point remainder for division by integer.
            #[inline]
            pub fn wrapping_rem_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_rem(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point left shift.
            #[inline]
            pub fn wrapping_shl(self, rhs: u32) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_shl(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point right shift.
            #[inline]
            pub fn wrapping_shr(self, rhs: u32) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_shr(self.to_bits(), rhs))
            }

            if_signed! {
                $Signedness =>
                /// Wrapping absolute value.
                #[inline]
                pub fn wrapping_abs(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::wrapping_abs(self.to_bits()))
                }
            }

            /// Overflowing negation.
            #[inline]
            pub fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_neg(self.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point addition.
            #[inline]
            pub fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_add(self.to_bits(), rhs.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point subtraction.
            #[inline]
            pub fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_sub(self.to_bits(), rhs.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point multiplication.
            #[inline]
            pub fn overflowing_mul(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                ($Fixed::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point division.
            #[inline]
            pub fn overflowing_div(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                ($Fixed::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point multiplication by integer.
            #[inline]
            pub fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_mul(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point division by integer.
            #[inline]
            pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_div(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point remainder for division by integer.
            #[inline]
            pub fn overflowing_rem_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_rem(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point left shift.
            #[inline]
            pub fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shl(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point right shift.
            #[inline]
            pub fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shr(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            if_signed! {
                $Signedness =>
                /// Overflowing absolute value.
                #[inline]
                pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = <$Inner>::overflowing_abs(self.to_bits());
                    ($Fixed::from_bits(ans), o)
                }
            }

            if_unsigned! {
                $Signedness => pass_method! {
                    concat!(
                        "Returns `true` if the fixed-point number is\n",
                        "2<sup><i>k</i></sup> for some <i>k</i>.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "// 3/8 is 0.0110\n",
                        "let three_eights = Fix::from_bits(0b0110);\n",
                        "// 1/2 is 0.1000\n",
                        "let half = Fix::from_bits(0b1000);\n",
                        "assert!(!three_eights.is_power_of_two());\n",
                        "assert!(half.is_power_of_two());\n",
                        "```\n"
                    ),
                    $Fixed($Inner) => fn is_power_of_two(self) -> bool
                }
            }

            if_unsigned! {
                $Signedness => pass_method! {
                    concat!(
                        "Returns the smallest power of two ≥ `self`.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "// 3/8 is 0.0110\n",
                        "let three_eights = Fix::from_bits(0b0110);\n",
                        "// 1/2 is 0.1000\n",
                        "let half = Fix::from_bits(0b1000);\n",
                        "assert_eq!(three_eights.next_power_of_two(), half);\n",
                        "assert_eq!(half.next_power_of_two(), half);\n",
                        "```\n"
                    ),
                    $Fixed($Inner) => fn next_power_of_two(self)
                }
            }

            if_unsigned! {
                $Signedness => doc_comment! {
                    concat!(
                        "Returns the smallest power of two ≥ `self`, or `None`\n",
                        "if the next power of two is too large to represent.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "// 3/8 is 0.0110\n",
                        "let three_eights = Fix::from_bits(0b0110);\n",
                        "// 1/2 is 0.1000\n",
                        "let half = Fix::from_bits(0b1000);\n",
                        "assert_eq!(three_eights.checked_next_power_of_two(), Some(half));\n",
                        "assert!(Fix::max_value().checked_next_power_of_two().is_none());\n",
                        "```\n"
                    ),
                    #[inline]
                    pub fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                        <$Inner>::checked_next_power_of_two(self.to_bits()).map($Fixed::from_bits)
                    }
                }
            }

            if_signed! {
                $Signedness => pass_method! {
                    concat!(
                        "Returns the absolute value.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert_eq!(Fix::from_int(5).unwrap().abs(), Fix::from_int(5).unwrap());\n",
                        "assert_eq!(Fix::from_int(-5).unwrap().abs(), Fix::from_int(5).unwrap());\n",
                        "```\n"
                    ),
                    $Fixed($Inner) => fn abs(self)
                }
            }

            if_signed! {
                $Signedness => doc_comment! {
                    concat!(
                        "Returns a number representing the sign of `self`.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert_eq!(Fix::from_int(5).unwrap().signum(), Fix::from_int(1).unwrap());\n",
                        "assert_eq!(Fix::from_int(0).unwrap().signum(), Fix::from_int(0).unwrap());\n",
                        "assert_eq!(Fix::from_int(-5).unwrap().signum(), Fix::from_int(-1).unwrap());\n",
                        "```\n"
                    ),
                    #[inline]
                    pub fn signum(self) -> $Fixed<Frac> {
                        match self.to_bits().cmp(&0) {
                            Ordering::Equal => $Fixed::from_bits(0),
                            Ordering::Greater => {
                                <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow")
                            }
                            Ordering::Less => {
                                <$Fixed<Frac> as FixedHelper<Frac>>::minus_one().expect("overflow")
                            }
                        }
                    }
                }
            }

            if_signed! {
                $Signedness => pass_method! {
                    concat!(
                        "Returns `true` if the number is > 0.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert!(Fix::from_int(5).unwrap().is_positive());\n",
                        "assert!(!Fix::from_int(0).unwrap().is_positive());\n",
                        "assert!(!Fix::from_int(-5).unwrap().is_positive());\n",
                        "```\n"
                    ),
                    $Fixed($Inner) => fn is_positive(self) -> bool
                }
            }

            if_signed! {
                $Signedness => pass_method! {
                    concat!(
                        "Returns `true` if the number is < 0.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert!(!Fix::from_int(5).unwrap().is_negative());\n",
                        "assert!(!Fix::from_int(0).unwrap().is_negative());\n",
                        "assert!(Fix::from_int(-5).unwrap().is_negative());\n",
                        "```\n"
                    ),
                    $Fixed($Inner) => fn is_negative(self) -> bool
                }
            }
        }
    };
}

fixed! { "An eight-bit fixed-point unsigned integer", FixedU8(u8, U8, 8), Unsigned }
fixed! { "A 16-bit fixed-point unsigned integer", FixedU16(u16, U16, 16), Unsigned }
fixed! { "A 32-bit fixed-point unsigned integer", FixedU32(u32, U32, 32), Unsigned }
fixed! { "A 64-bit fixed-point unsigned integer", FixedU64(u64, U64, 64), Unsigned }
fixed! { "A 128-bit fixed-point unsigned integer", FixedU128(u128, U128, 128), Unsigned }
fixed! { "An eight-bit fixed-point signed integer", FixedI8(i8, U8, 8), Signed }
fixed! { "A 16-bit fixed-point signed integer", FixedI16(i16, U16, 16), Signed }
fixed! { "A 32-bit fixed-point signed integer", FixedI32(i32, U32, 32), Signed }
fixed! { "A 64-bit fixed-point signed integer", FixedI64(i64, U64, 64), Signed }
fixed! { "A 128-bit fixed-point signed integer", FixedI128(i128, U128, 128), Signed }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn rounding() {
        use frac::{U16, U32};

        type I0F32 = FixedI32<U32>;

        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        type U0F32 = FixedU32<U32>;

        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        type I16F16 = FixedI32<U16>;

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);

        // -3.5 + Δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -3);

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 3.5 - Δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        // 3.5 + Δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        type U16F16 = FixedU32<U16>;

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 3.5 - Δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        // 3.5 + Δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
    }
}
