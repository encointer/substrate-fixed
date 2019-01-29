// Copyright © 2018–2019 Trevor Spiteri

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

All lossless infallible conversions between fixed-point numbers and
numeric primitives are implemented. That is, you can use [`From`] or
[`Into`] for the conversions that always work without losing any bits.

## Quick example

```rust
// 20 integer bits, 12 fractional bits
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// convert to i32, taking the ceil
assert_eq!(six_and_third.ceil().to_int(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
[`FixedI32<frac::U12>`][`FixedI32`]. The unsigned counterpart would be
[`U20F12`]. Aliases are provided for all combinations of integer and
fractional bits adding up to a total of eight, 16, 32, 64 or 128 bits.

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.1.6"
```

If you are using the 2015 Rust edition, you also need to declare it by
adding this to your crate root (usually *lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.28.0 or later.

## Optional features

The *fixed* crate has two optional feature:

 1. `f16`, disabled by default. This provides conversion to/from
    [`f16`]. This features requires the [*half* crate].
 2. `serde`, disabled by default. This provides serialization support
    for the fixed-point types. This feature requires the
    [*serde* crate].

To enable features, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "0.1.6"
features = ["f16", "serde"]
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
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`FixedI128`]: struct.FixedI128.html
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
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: types/type.I20F12.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`U20F12`]: types/type.U20F12.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.1.6")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(nightly_repr_transparent, feature(repr_transparent))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

#[cfg(feature = "f16")]
extern crate half;
#[cfg(feature = "serde")]
extern crate serde;
extern crate typenum;

macro_rules! if_signed {
    (Signed; $($rem:tt)+) => {
        $($rem)+
    };
    (Unsigned; $($rem:tt)+) => {
    };
}
macro_rules! if_unsigned {
    (Signed; $($rem:tt)+) => {
    };
    (Unsigned; $($rem:tt)+) => {
        $($rem)+
    };
}
macro_rules! if_signed_unsigned {
    (Signed, $signed:expr, $unsigned:expr) => {
        $signed
    };
    (Unsigned, $signed:expr, $unsigned:expr) => {
        $unsigned
    };
    ($Signedness:tt, $signed:expr, $unsigned:expr,) => {
        if_signed_unsigned!($Signedness, $signed, $unsigned)
    };
}

mod arith;
mod cmp;
mod convert;
mod display;
pub mod frac;
pub mod sealed;
mod sealed_fixed;
mod sealed_float;
mod sealed_int;
#[cfg(feature = "serde")]
mod serdeize;
pub mod types;
mod wide_div;

use arith::MulDivDir;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
#[cfg(feature = "f16")]
use half::f16;
use sealed::{Fixed, Float, Int, SealedFixed, SealedFloat, SealedInt};

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
        if_signed! { $Signedness; pass_method! { $signed, $($tt)* } }
        if_unsigned! { $Signedness; pass_method! { $unsigned, $($tt)* } }
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
        if_signed! { $Signedness; doc_comment! { $signed, $($tt)* } }
        if_unsigned! { $Signedness; doc_comment! { $unsigned, $($tt)* } }
    };
}

macro_rules! deprecated_from_float {
    (fn $method:ident($Float:ident) -> $Fixed:ident<$Frac:ident>) => {
        doc_comment! {
            concat!(
                "Creates a fixed-point number from `", stringify!($Float), "`.\n",
                "\n",
                "This method has been replaced by [`checked_from_float`].\n",
                "\n",
                "[`checked_from_float`]: #method.checked_from_float\n",
            ),
            #[deprecated(since = "0.2.0", note = "replaced by checked_from_float")]
            #[inline]
            pub fn $method(val: $Float) -> Option<$Fixed<$Frac>> {
                <$Fixed<$Frac>>::checked_from_float(val)
            }
        }
    };
}

macro_rules! deprecated_to_float {
    (fn $method:ident($Fixed:ident<$Frac:ident>) -> $Float:ident) => {
        doc_comment! {
            concat!(
                "Converts the fixed-point number to `", stringify!($Float), "`.\n",
                "\n",
                "This method has been replaced by [`to_float`].\n",
                "\n",
                "[`to_float`]: #method.to_float\n",
            ),
            #[deprecated(since = "0.2.0", note = "replaced by to_float")]
            #[inline]
            pub fn $method(self) -> $Float {
                self.to_float()
            }
        }
    };
}

macro_rules! fixed {
    ($description:expr, $Fixed:ident($Inner:ty, $Len:tt, $nbits:expr), $Signedness:tt) => {
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
                "[typenum crate]: https://crates.io/crates/typenum\n",
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
                    "```\n",
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
                    "```\n",
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
                    "```\n",
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
                    "assert_eq!(Fix::int_bits(), ", stringify!($nbits), " - 6);\n",
                    "```\n",
                ),
                #[inline]
                pub fn int_bits() -> u32 {
                    <Self as SealedFixed>::int_bits()
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
                    "```\n",
                ),
                #[inline]
                pub fn frac_bits() -> u32 {
                    <Self as SealedFixed>::frac_bits()
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
                    "```\n",
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
                    "// 2 is 0010.0000\n",
                    "assert_eq!(Fix::from_int(2).to_bits(), 0b10_0000);\n",
                    "```\n",
                ),
                #[inline]
                pub fn to_bits(self) -> $Inner {
                    (self.0).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from another fixed-point number.\n",
                    "\n",
                    "The source value does not need to have the same fixed-point type as\n",
                    "the destination value.\n",
                    "\n",
                    "This method truncates the extra fractional bits in the source value.\n",
                    "For example, if the source type has 24 fractional bits and the destination\n",
                    "type has 10 fractional bits, then 14 fractional bits will be truncated.\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "If the value is too large to fit, the method panics in debug mode.\n",
                    "In release mode, the method may either panic or wrap the value,\n",
                    "with the current implementation wrapping the value.\n",
                    "It is not considered a breaking change if in the future the method\n",
                    "panics even in release mode; if wrapping is the required behavior\n",
                    "use [`wrapping_from_fixed`] instead.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "type Src = fixed::FixedI32<frac::U16>;\n",
                    "type Fix = fixed::", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 1.1100, that is Src::from_bits(0b111 << (16 - 2))\n",
                    "// or Fix::from_bits(0b111<< (4 - 2))\n",
                    "let src = Src::from_bits(0b111 << (16 - 2));\n",
                    "let expected = Fix::from_bits(0b111 << (4 - 2));\n",
                    "assert_eq!(Fix::from_fixed(src), expected);\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::from_fixed(-src), -expected);\n",
                        "",
                    ),
                    "// src >> 4 is 0.0001_1100, which for Fix is truncated to 0000.0001\n",
                    "assert_eq!(Fix::from_fixed(src >> 4), Fix::from_bits(1));\n",
                    "```\n",
                    "[`wrapping_from_fixed`]: #method.wrapping_from_fixed\n",
                ),
                #[inline]
                pub fn from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    let (wrapped, overflow) = $Fixed::overflowing_from_fixed(val);
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("{} overflows", val);
                        }
                    }
                    let _ = overflow;
                    wrapped
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from another fixed-point number if it fits.\n",
                    "\n",
                    "The source value does not need to have the same fixed-point type as\n",
                    "the destination value.\n",
                    "\n",
                    "This method truncates the extra fractional bits in the source value.\n",
                    "For example, if the source type has 24 fractional bits and the destination\n",
                    "type has 10 fractional bits, then 14 fractional bits will be truncated.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Src = fixed::FixedI32<frac::U16>;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 1.1100, that is Src::from_bits(0b111 << (16 - 2))\n",
                    "// or Fix::from_bits(0b111<< (4 - 2))\n",
                    "let src = Src::from_bits(0b111 << (16 - 2));\n",
                    "let expected = Fix::from_bits(0b111 << (4 - 2));\n",
                    "assert_eq!(Fix::checked_from_fixed(src), Some(expected));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::checked_from_fixed(-src), Some(-expected));\n",
                        "",
                    ),
                    "let too_large = ", stringify!($Fixed), "::<frac::U3>::max_value();\n",
                    "assert!(Fix::checked_from_fixed(too_large).is_none());\n",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "let too_small = ", stringify!($Fixed), "::<frac::U3>::min_value();\n",
                            "assert!(Fix::checked_from_fixed(too_small).is_none());\n",
                        ),
                        "",
                    ),
                    "```\n",
                ),
                #[inline]
                pub fn checked_from_fixed<F>(val: F) -> Option<$Fixed<Frac>>
                where
                    F: Fixed,
                {
                    let (wrapped, overflow) = $Fixed::overflowing_from_fixed(val);
                    if overflow { None } else { Some(wrapped) }
                }
            }

            doc_comment! {
               concat!(
                    "Creates a fixed-point number from another fixed-point number,\n",
                    "saturating the value if it does not fit.\n",
                    "\n",
                    "The source value does not need to have the same fixed-point type as\n",
                    "the destination value.\n",
                    "\n",
                    "This method truncates the extra fractional bits in the source value.\n",
                    "For example, if the source type has 24 fractional bits and the destination\n",
                    "type has 10 fractional bits, then 14 fractional bits will be truncated.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Src = fixed::FixedI32<frac::U16>;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 1.1100, that is Src::from_bits(0b111 << (16 - 2))\n",
                    "// or Fix::from_bits(0b111<< (4 - 2))\n",
                    "let src = Src::from_bits(0b111 << (16 - 2));\n",
                    "let expected = Fix::from_bits(0b111 << (4 - 2));\n",
                    "assert_eq!(Fix::saturating_from_fixed(src), expected);\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::saturating_from_fixed(-src), -expected);\n",
                        "",
                    ),
                    "let too_large = ", stringify!($Fixed), "::<frac::U3>::max_value();\n",
                    "assert_eq!(Fix::saturating_from_fixed(too_large), Fix::max_value());\n",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "let too_small = ", stringify!($Fixed), "::<frac::U3>::min_value();\n",
                        ),
                        "let too_small = Src::from_bits(-1);\n",
                    ),
                    "assert_eq!(Fix::saturating_from_fixed(too_small), Fix::min_value());\n",
                    "```\n",
                ),
                #[inline]
                pub fn saturating_from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();
                    let saturated = if val.to_bits().neg_abs().0 {
                        $Fixed::min_value()
                    } else {
                        $Fixed::max_value()
                    };
                    let (neg, abs_128, overflow) =
                        <F as SealedFixed>::to_neg_abs_overflow(val, frac_bits, int_bits);
                    if overflow {
                        return saturated;
                    }
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                return saturated;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        return saturated;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    SealedFixed::from_bits(bits)
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from another fixed-point number,\n",
                    "wrapping the value on overflow.\n",
                    "\n",
                    "The source value does not need to have the same fixed-point type as\n",
                    "the destination value.\n",
                    "\n",
                    "This method truncates the extra fractional bits in the source value.\n",
                    "For example, if the source type has 24 fractional bits and the destination\n",
                    "type has 10 fractional bits, then 14 fractional bits will be truncated.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Src = fixed::FixedI32<frac::U16>;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 1.1100, that is Src::from_bits(0b111 << (16 - 2))\n",
                    "// or Fix::from_bits(0b111<< (4 - 2))\n",
                    "let src = Src::from_bits(0b111 << (16 - 2));\n",
                    "let expected = Fix::from_bits(0b111 << (4 - 2));\n",
                    "assert_eq!(Fix::wrapping_from_fixed(src), expected);\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::wrapping_from_fixed(-src), -expected);\n",
                        "",
                    ),
                    "// integer 0b1101 << (", stringify!($nbits), " - 7) will wrap to fixed-point 1010...\n",
                    "let large = ", stringify!($Fixed), "::<frac::U0>::from_bits(0b1101 << (", stringify!($nbits), " - 7));\n",
                    "let wrapped = Fix::from_bits(0b1010 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::wrapping_from_fixed(large), wrapped);\n",
                    "```\n",
                ),
                #[inline]
                pub fn wrapping_from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    $Fixed::overflowing_from_fixed(val).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from another fixed-point number.\n",
                    "\n",
                    "Returns a tuple of the fixed-point number and a [`bool`] indicating whether\n",
                    "an overflow has occurred. On overflow, the wrapped value is returned.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Src = fixed::FixedI32<frac::U16>;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 1.1100, that is Src::from_bits(0b111 << (16 - 2))\n",
                    "// or Fix::from_bits(0b111<< (4 - 2))\n",
                    "let src = Src::from_bits(0b111 << (16 - 2));\n",
                    "let expected = Fix::from_bits(0b111 << (4 - 2));\n",
                    "assert_eq!(Fix::overflowing_from_fixed(src), (expected, false));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::overflowing_from_fixed(-src), (-expected, false));\n",
                        "",
                    ),
                    "// integer 0b1101 << (", stringify!($nbits), " - 7) will wrap to fixed-point 1010...\n",
                    "let large = ", stringify!($Fixed), "::<frac::U0>::from_bits(0b1101 << (", stringify!($nbits), " - 7));\n",
                    "let wrapped = Fix::from_bits(0b1010 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::overflowing_from_fixed(large), (wrapped, true));\n",
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                ),
                #[inline]
                pub fn overflowing_from_fixed<F>(val: F) -> ($Fixed<Frac>, bool)
                where
                    F: Fixed,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();

                    let (neg, abs_128, mut overflow) =
                        <F as SealedFixed>::to_neg_abs_overflow(val, frac_bits, int_bits);
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                overflow = true;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        overflow = true;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    (SealedFixed::from_bits(bits), overflow)
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from an integer.\n",
                    "\n",
                    "The integer value can be of type [`bool`], [`i8`], [`i16`], [`i32`],",
                    "[`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "If the value is too large to fit, the method panics in debug mode.\n",
                    "In release mode, the method may either panic or wrap the value,\n",
                    "with the current implementation wrapping the value.\n",
                    "It is not considered a breaking change if in the future the method\n",
                    "panics even in release mode; if wrapping is the required behavior\n",
                    "use [`wrapping_from_int`] instead.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 3 is 0011.0000, that is from_bits(3 << 4)\n",
                    "assert_eq!(Fix::from_int(3), Fix::from_bits(3 << 4));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::from_int(-3), Fix::from_bits(-3 << 4));\n",
                        "",
                    ),
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html\n",
                    "[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html\n",
                    "[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html\n",
                    "[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html\n",
                    "[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html\n",
                    "[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html\n",
                    "[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html\n",
                    "[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html\n",
                    "[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html\n",
                    "[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html\n",
                    "[`wrapping_from_int`]: #method.wrapping_from_int\n",
                ),
                #[inline]
                pub fn from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    let (wrapped, overflow) = $Fixed::overflowing_from_int(val);
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("{} overflows", val);
                        }
                    }
                    let _ = overflow;
                    wrapped
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from an integer if it fits.\n",
                    "\n",
                    "The integer value can be of type [`bool`], [`i8`], [`i16`], [`i32`],",
                    "[`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use std::", stringify!($Inner), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 3 is 0011.0000, that is from_bits(3 << 4)\n",
                    "assert_eq!(Fix::checked_from_int(3), Some(Fix::from_bits(3 << 4)));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::checked_from_int(-3), Some(Fix::from_bits(-3 << 4)));\n",
                        "",
                    ),
                    "let too_large = ", stringify!($Inner), "::max_value();\n",
                    "assert!(Fix::checked_from_int(too_large).is_none());\n",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "let too_small = ", stringify!($Inner), "::min_value();\n",
                            "assert!(Fix::checked_from_int(too_small).is_none());\n",
                        ),
                        "",
                    ),
                    "```\n",
                     "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html\n",
                    "[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html\n",
                    "[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html\n",
                    "[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html\n",
                    "[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html\n",
                    "[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html\n",
                    "[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html\n",
                    "[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html\n",
                    "[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html\n",
                    "[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html\n",
               ),
                #[inline]
                pub fn checked_from_int<I>(val: I) -> Option<$Fixed<Frac>>
                where
                    I: Int,
                {
                    let (wrapped, overflow) = $Fixed::overflowing_from_int(val);
                    if overflow { None } else { Some(wrapped) }
                }
            }

            doc_comment! {
               concat!(
                    "Creates a fixed-point number from an integer,\n",
                    "saturating the value if it does not fit.\n",
                    "\n",
                    "The integer value can be of type [`bool`], [`i8`], [`i16`], [`i32`],",
                    "[`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use std::", stringify!($Inner), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 3 is 0011.0000, that is from_bits(3 << 4)\n",
                    "assert_eq!(Fix::saturating_from_int(3), Fix::from_bits(3 << 4));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::saturating_from_int(-3), Fix::from_bits(-3 << 4));\n",
                        "",
                    ),
                    "let too_large = ", stringify!($Inner), "::max_value();\n",
                    "assert_eq!(Fix::saturating_from_int(too_large), Fix::max_value());\n",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "let too_small = ", stringify!($Inner), "::min_value();\n",
                        ),
                        "let too_small = -1;\n",
                    ),
                    "assert_eq!(Fix::saturating_from_int(too_small), Fix::min_value());\n",
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html\n",
                    "[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html\n",
                    "[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html\n",
                    "[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html\n",
                    "[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html\n",
                    "[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html\n",
                    "[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html\n",
                    "[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html\n",
                    "[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html\n",
                    "[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html\n",
                ),
                #[inline]
                pub fn saturating_from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();
                    let saturated = if val.neg_abs().0 {
                        $Fixed::min_value()
                    } else {
                        $Fixed::max_value()
                    };
                    let (neg, abs_128, overflow) =
                        <I as SealedInt>::to_fixed_neg_abs_overflow(val, frac_bits, int_bits);
                    if overflow {
                        return saturated;
                    }
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                return saturated;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        return saturated;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    SealedFixed::from_bits(bits)
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from an integer,\n",
                    "wrapping the value on overflow.\n",
                    "\n",
                    "The integer value can be of type [`bool`], [`i8`], [`i16`], [`i32`],",
                    "[`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 3 is 0011.0000, that is from_bits(3 << 4)\n",
                    "assert_eq!(Fix::wrapping_from_int(3), Fix::from_bits(3 << 4));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::wrapping_from_int(-3), Fix::from_bits(-3 << 4));\n",
                        "",
                    ),
                    "// integer 0b1101 << (", stringify!($nbits), " - 7) will wrap to fixed-point 1010...\n",
                    "let large: ", stringify!($Inner), " = 0b1101 << (", stringify!($nbits), " - 7);\n",
                    "let wrapped = Fix::from_bits(0b1010 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::wrapping_from_int(large), wrapped);\n",
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html\n",
                    "[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html\n",
                    "[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html\n",
                    "[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html\n",
                    "[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html\n",
                    "[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html\n",
                    "[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html\n",
                    "[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html\n",
                    "[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html\n",
                    "[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html\n",
                ),
                #[inline]
                pub fn wrapping_from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    $Fixed::overflowing_from_int(val).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from an integer.\n",
                    "\n",
                    "Returns a tuple of the fixed-point number and a [`bool`] indicating whether\n",
                    "an overflow has occurred. On overflow, the wrapped value is returned.\n",
                    "\n",
                    "The integer value can be of type [`bool`], [`i8`], [`i16`], [`i32`],",
                    "[`i64`], [`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 3 is 0011.0000, that is from_bits(3 << 4)\n",
                    "assert_eq!(Fix::overflowing_from_int(3), (Fix::from_bits(3 << 4), false));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::overflowing_from_int(-3), (Fix::from_bits(-3 << 4), false));\n",
                        "",
                    ),
                    "// integer 0b1101 << (", stringify!($nbits), " - 7) will wrap to fixed-point 1010...\n",
                    "let large: ", stringify!($Inner), " = 0b1101 << (", stringify!($nbits), " - 7);\n",
                    "let wrapped = Fix::from_bits(0b1010 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::overflowing_from_int(large), (wrapped, true));\n",
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html\n",
                    "[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html\n",
                    "[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html\n",
                    "[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html\n",
                    "[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html\n",
                    "[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html\n",
                    "[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html\n",
                    "[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html\n",
                    "[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html\n",
                    "[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html\n",
                ),
                #[inline]
                pub fn overflowing_from_int<I>(val: I) -> ($Fixed<Frac>, bool)
                where
                    I: Int,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();

                    let (neg, abs_128, mut overflow) =
                        <I as SealedInt>::to_fixed_neg_abs_overflow(val, frac_bits, int_bits);
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                overflow = true;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        overflow = true;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    (SealedFixed::from_bits(bits), overflow)
                }
            }

            doc_comment! {
                concat!(r#"

Converts the fixed-point number of type `"#, stringify!($Fixed), r#"`
to an integer of type [`"#, stringify!($Inner), r#"`] truncating the
fractional bits.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.to_int(), 2);"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).to_int(), -3);"#, ""
), r#"
```

[`"#, stringify!($Inner), r#"`]: https://doc.rust-lang.org/nightly/std/primitive."#, stringify!($Inner), r#".html
"#,
                ),
                #[inline]
                pub fn to_int(self) -> $Inner {
                    let int = self.int().to_bits();
                    if Self::frac_bits() < $nbits {
                        int >> Self::frac_bits()
                    } else {
                        int
                    }
                }
            }

            doc_comment! {
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "`, rounding towards +∞.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.ceil().to_int() instead")]
                #[inline]
                pub fn to_int_ceil(self) -> $Inner {
                    if let Some(ceil) = self.checked_ceil() {
                        ceil.to_int()
                    } else {
                        self.floor().to_int() + 1
                    }
                }
            }

            doc_comment! {
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "` rounding towards −∞.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.floor().to_int() instead")]
                #[inline]
                pub fn to_int_floor(self) -> $Inner {
                    if let Some(floor) = self.checked_floor() {
                        floor.to_int()
                    } else {
                        self.ceil().to_int() - 1
                    }
                }
            }

            doc_comment! {
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "` rounding towards the nearest. Ties are rounded away from zero.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.round().to_int() instead")]
                #[inline]
                pub fn to_int_round(self) -> $Inner {
                    if let Some(round) = self.checked_round() {
                        round.to_int()
                    } else if let Some(floor) = self.checked_floor() {
                        floor.to_int() + 1
                    } else {
                        self.ceil().to_int() - 1
                    }
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from a floating-point number.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "This method always panics if the value is not [finite].\n",
                    "\n",
                    "If the value is too large to fit, the method panics in debug mode.\n",
                    "In release mode, the method may either panic or wrap the value,\n",
                    "with the current implementation wrapping the value.\n",
                    "It is not considered a breaking change if in the future the method\n",
                    "panics even in release mode; if wrapping is the required behavior\n",
                    "use [`wrapping_from_float`] instead.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "assert_eq!(Fix::from_float(1.75f32), Fix::from_bits(28));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::from_float(-1.75f64), Fix::from_bits(-28));\n",
                        "assert_eq!(Fix::from_float(1.75f64), Fix::from_bits(28));\n",
                    ),
                    "// 1e-10 is too small for four fractional bits\n",
                    "assert_eq!(Fix::from_float(1e-10), Fix::from_bits(0));\n",
                    "```\n",
                    "\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                    "[`wrapping_from_float`]: #method.wrapping_from_float\n",
                    "[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite\n",
                ),
                #[inline]
                pub fn from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    let (wrapped, overflow) = $Fixed::overflowing_from_float(val);
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("{} overflows", val);
                        }
                    }
                    let _ = overflow;
                    wrapped
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from a floating-point number,\n",
                    "or returns [`None`] if the value is not finite or does not fit.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use std::f64;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "assert_eq!(Fix::checked_from_float(1.75f32), Some(Fix::from_bits(28)));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::checked_from_float(-1.75f64), Some(Fix::from_bits(-28)));\n",
                        "assert_eq!(Fix::checked_from_float(1.75f64), Some(Fix::from_bits(28)));\n",
                    ),
                    "// 1e-10 is too small for four fractional bits\n",
                    "assert_eq!(Fix::checked_from_float(1e-10), Some(Fix::from_bits(0)));\n",
                    "// 2e38 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                    "assert!(Fix::checked_from_float(2e38).is_none());\n",
                    "assert!(Fix::checked_from_float(f64::NEG_INFINITY).is_none());\n",
                    "assert!(Fix::checked_from_float(f64::NAN).is_none());\n",
                    "```\n",
                    "\n",
                    "[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                ),
                #[inline]
                pub fn checked_from_float<F>(val: F) -> Option<$Fixed<Frac>>
                where
                    F: Float,
                {
                    if !val.is_finite() {
                        return None;
                    }
                    let (wrapped, overflow) = $Fixed::overflowing_from_float(val);
                    if overflow {
                        None
                    } else {
                        Some(wrapped)
                    }
                }
            }

            doc_comment! {
               concat!(
                    "Creates a fixed-point number from a floating-point number,\n",
                    "saturating the value if it does not fit.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "This method panics if the value is [NaN].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "use std::f64;\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "assert_eq!(Fix::saturating_from_float(1.75f32), Fix::from_bits(28));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::saturating_from_float(-1.75f64), Fix::from_bits(-28));\n",
                        "assert_eq!(Fix::saturating_from_float(1.75f64), Fix::from_bits(28));\n",
                    ),
                    "// 1e-10 is too small for four fractional bits\n",
                    "assert_eq!(Fix::saturating_from_float(1e-10), Fix::from_bits(0));\n",
                    "// 2e38 is too large for ", stringify!($Fixed), "<frac::U4>\n",
                    "assert_eq!(Fix::saturating_from_float(2e38), Fix::max_value());\n",
                    "assert_eq!(Fix::saturating_from_float(f64::NEG_INFINITY), Fix::min_value());\n",
                    "```\n",
                    "\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                    "[NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan\n",
                ),
                #[inline]
                pub fn saturating_from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();
                    let saturated = if val.is_sign_positive() {
                        $Fixed::max_value()
                    } else {
                        $Fixed::min_value()
                    };
                    if !val.is_finite() {
                        return saturated;
                    }
                    let (neg, abs_128, overflow) =
                        <F as SealedFloat>::to_fixed_neg_abs_overflow(val, frac_bits, int_bits);
                    if overflow {
                        return saturated;
                    }
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                return saturated;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        return saturated;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    SealedFixed::from_bits(bits)
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from a floating-point number,\n",
                    "wrapping the value on overflow.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "This method panics if the value is not [finite].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let from_bits = Fix::from_bits(28);\n",
                    "assert_eq!(Fix::wrapping_from_float(1.75f32), from_bits);\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::wrapping_from_float(-1.75f64), -from_bits);\n",
                        "assert_eq!(Fix::wrapping_from_float(1.75f64), from_bits);\n",
                    ),
                    "// 1e-10 is too small for four fractional bits\n",
                    "assert_eq!(Fix::wrapping_from_float(1e-10), 0);\n",
                    "// 1.75 << (", stringify!($nbits), " - 4) wraps to binary 11000...\n",
                    "let large = 1.75 * 2f32.powi(", stringify!($nbits), " - 4);\n",
                    "let wrapped = Fix::from_bits(0b1100 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::wrapping_from_float(large), wrapped);\n",
                    "```\n",
                    "\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                    "[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite\n",
                ),
                #[inline]
                pub fn wrapping_from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    $Fixed::overflowing_from_float(val).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number from a floating-point number.\n",
                    "\n",
                    "Returns a tuple of the fixed-point number and a [`bool`] indicating whether\n",
                    "an overflow has occurred. On overflow, the wrapped value is returned.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
                    "\n",
                    "This method rounds to the nearest, with ties rounding to even.\n",
                    "\n",
                    "# Panics\n",
                    "\n",
                    "This method panics if the value is not [finite].\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 1.75 is 0001.1100, that is from_bits(28)\n",
                    "let from_bits = Fix::from_bits(28);\n",
                    "assert_eq!(Fix::overflowing_from_float(1.75f32), (from_bits, false));\n",
                    if_signed_unsigned!(
                        $Signedness,
                        "assert_eq!(Fix::overflowing_from_float(-1.75f64), (-from_bits, false));\n",
                        "assert_eq!(Fix::overflowing_from_float(1.75f64), (from_bits, false));\n",
                    ),
                    "// 1e-10 is too small for four fractional bits\n",
                    "assert_eq!(Fix::overflowing_from_float(1e-10), (Fix::from_bits(0), false));\n",
                    "// 1.75 << (", stringify!($nbits), " - 4) overflows and wraps to binary 11000...\n",
                    "let large = 1.75 * 2f32.powi(", stringify!($nbits), " - 4);\n",
                    "let wrapped = Fix::from_bits(0b1100 << (", stringify!($nbits), " - 4));\n",
                    "assert_eq!(Fix::overflowing_from_float(large), (wrapped, true));\n",
                    "```\n",
                    "\n",
                    "[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                    "[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite\n",
                ),
                #[inline]
                pub fn overflowing_from_float<F>(val: F) -> ($Fixed<Frac>, bool)
                where
                    F: Float,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();

                    if !val.is_finite() {
                        panic!("{} is not finite", val);
                    }
                    let (neg, abs_128, mut overflow) =
                        <F as SealedFloat>::to_fixed_neg_abs_overflow(val, frac_bits, int_bits);
                    let abs_bits =
                        abs_128 as <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned;

                    if <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::is_signed() {
                        // most significant bit (msb) can be one only for min value,
                        // that is for a negative value with only the msb true.
                        let msb =
                            <<$Fixed<Frac> as SealedFixed>::Bits as SealedInt>::Unsigned::msb();
                        if abs_bits & msb != 0 {
                            if !neg || abs_bits != msb {
                                overflow = true;
                            }
                        }
                    } else if neg && abs_bits != 0 {
                        overflow = true;
                    }
                    let bits = if neg {
                        abs_bits.wrapping_neg()
                    } else {
                        abs_bits
                    } as <$Fixed<Frac> as SealedFixed>::Bits;

                    (SealedFixed::from_bits(bits), overflow)
                }
            }

            #[cfg(feature = "f16")]
            deprecated_from_float! { fn from_f16(f16) -> $Fixed<Frac> }
            deprecated_from_float! { fn from_f32(f32) -> $Fixed<Frac> }
            deprecated_from_float! { fn from_f64(f64) -> $Fixed<Frac> }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number to a floating-point number.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
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
                    "assert_eq!(Fix::from_bits(28).to_float::<f32>(), 1.75f32);\n",
                    "assert_eq!(Fix::from_bits(-28).to_float::<f64>(), -1.75f64);\n",
                    "```\n",
                    "\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                ),
                concat!(
                    "Converts the fixed-point number to a floating-point number.\n",
                    "\n",
                    "The floating-point value can be of type [`f32`] or [`f64`].\n",
                    "If the [`f16` feature] is enabled, it can also be of type [`f16`].\n",
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
                    "assert_eq!(Fix::from_bits(28).to_float::<f32>(), 1.75f32);\n",
                    "assert_eq!(Fix::from_bits(28).to_float::<f64>(), 1.75f64);\n",
                    "```\n",
                    "\n",
                    "[`f16` feature]: index.html#optional-features\n",
                    "[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html\n",
                    "[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html\n",
                    "[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html\n",
                ),
                pub fn to_float<F>(self) -> F
                where
                    F: Float,
                {
                    let frac_bits = Self::frac_bits();
                    let int_bits = Self::int_bits();
                    let (neg, abs) = self.to_bits().neg_abs();
                    SealedFloat::from_neg_abs(neg, u128::from(abs), frac_bits, int_bits)
                }
            }

            #[cfg(feature = "f16")]
            deprecated_to_float! { fn to_f16($Fixed<Frac>) -> f16 }
            deprecated_to_float! { fn to_f32($Fixed<Frac>) -> f32 }
            deprecated_to_float! { fn to_f64($Fixed<Frac>) -> f64 }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the integer part.\n",
                    "\n",
                    "Note that since the numbers are stored in two’s\n",
                    "complement, negative numbers with non-zero fractional\n",
                    "parts will be rounded towards −∞, except in the case\n",
                    "where there are no integer bits, that is `",
                    stringify!($Fixed), "<U", stringify!($nbits), ">`,\n",
                    "where the return value is always zero.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000\n",
                    "let two = Fix::from_int(2);\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "// 1101.0000\n",
                    "let neg_three = Fix::from_int(-3);\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.int(), neg_three);\n",
                    "```\n",
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
                    "let two = Fix::from_int(2);\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "```\n",
                ),
                #[inline]
                pub fn int(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits() & Self::int_mask())
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
                    stringify!($Fixed), "<U", stringify!($nbits), ">`,\n",
                    "where the return value is always equal to `self`.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0000.0100\n",
                    "let quarter = Fix::from_int(1) / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "// 0000.1100\n",
                    "let three_quarters = quarter * 3;\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.frac(), three_quarters);\n",
                    "```\n",
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
                    "let quarter = Fix::from_int(1) / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "```\n",
                ),
                #[inline]
                pub fn frac(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits() & Self::frac_mask())
                }
            }

            doc_comment! {
                concat!(r#"
Rounds to the next integer towards +∞.

# Panics

If the result is too large to fit, the method panics in debug mode. In
release mode, the method may either panic or wrap the value, with the
current implementation wrapping the value. It is not considered a
breaking change if in the future the method panics even in release
mode; if wrapping is the required behavior use [`wrapping_ceil`]
instead.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.ceil(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).ceil(), Fix::from_int(-2));"#, ""
), r#"
```

[`wrapping_ceil`]: #method.wrapping_ceil
"#,
                ),
                #[inline]
                pub fn ceil(self) -> $Fixed<Frac> {
                    let (ceil, overflow) = self.overflowing_ceil();
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("overflow");
                        }
                    }
                    let _ = overflow;
                    ceil
                }
            }

            doc_comment! {
                concat!(r#"
Rounds to the next integer towards −∞."#,
if_signed_unsigned!($Signedness, r#"

# Panics

If the result is too large to fit, the method panics in debug mode. In
release mode, the method may either panic or wrap the value, with the
current implementation wrapping the value. It is not considered a
breaking change if in the future the method panics even in release
mode; if wrapping is the required behavior use [`wrapping_floor`]
instead.

Overflow can only occur when there are zero integer bits."#, ""
), r#"

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.floor(), Fix::from_int(2));"#,
if_signed_unsigned!($Signedness, concat!(r#"
assert_eq!((-two_half).floor(), Fix::from_int(-3));"#), ""
), r#"
```

[`wrapping_floor`]: #method.wrapping_floor
"#,
                ),
                #[inline]
                pub fn floor(self) -> $Fixed<Frac> {
                    let (floor, overflow) = self.overflowing_floor();
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("overflow");
                        }
                    }
                    let _ = overflow;
                    floor
                }
            }

            doc_comment! {
                concat!(r#"
Rounds to the nearest integer, with ties rounded away from zero.

# Panics

If the result is too large to fit, the method panics in debug mode. In
release mode, the method may either panic or wrap the value, with the
current implementation wrapping the value. It is not considered a
breaking change if in the future the method panics even in release
mode; if wrapping is the required behavior use [`wrapping_round`]
instead.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.round(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).round(), Fix::from_int(-3));"#, ""
), r#"
```

[`wrapping_round`]: #method.wrapping_round
"#,
                ),
                #[inline]
                pub fn round(self) -> $Fixed<Frac> {
                    let (round, overflow) = self.overflowing_round();
                    #[cfg(debug_assertions)]
                    {
                        if overflow {
                            panic!("overflow");
                        }
                    }
                    let _ = overflow;
                    round
                }
            }

            doc_comment! {
                concat!(r#"
Checked ceil. Rounds to the next integer towards +∞, returning [`None`] on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_ceil(), Some(Fix::from_int(3)));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).checked_ceil(), Some(Fix::from_int(-2)));"#, ""
), r#"
assert!(Fix::max_value().checked_ceil().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
"#,
                ),
                #[inline]
                pub fn checked_ceil(self) -> Option<$Fixed<Frac>> {
                    let (ceil, overflow) = self.overflowing_ceil();
                    if overflow { None } else { Some(ceil) }
                }
            }

            doc_comment! {
                concat!(if_signed_unsigned!($Signedness, r#"
Checked floor. Rounds to the next integer towards −∞, returning [`None`] on overflow.

Overflow can only occur when there are zero integer bits.
"#, r#"
Checked floor. Rounds to the next integer towards −∞.
Always returns [`Some`] for unsigned values.
"#), r#"

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_floor(), Some(Fix::from_int(2)));"#,
if_signed_unsigned!($Signedness, concat!(r#"
assert_eq!((-two_half).checked_floor(), Some(Fix::from_int(-3)));
type AllFrac = "#, stringify!($Fixed), "<frac::", stringify!($Len), r#">;
assert!(AllFrac::min_value().checked_floor().is_none());"#), ""
), r#"
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`Some`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.Some
"#,
                ),
                #[inline]
                pub fn checked_floor(self) -> Option<$Fixed<Frac>> {
                    let (floor, overflow) = self.overflowing_floor();
                    if overflow { None } else { Some(floor) }
                }
            }

            doc_comment! {
                concat!(r#"
Checked round. Rounds to the nearest integer, with ties rounded away from
zero, returning [`None`] on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_round(), Some(Fix::from_int(3)));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).checked_round(), Some(Fix::from_int(-3)));"#, ""
), r#"
assert!(Fix::max_value().checked_round().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`Some`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.Some
"#,
                ),
                #[inline]
                pub fn checked_round(self) -> Option<$Fixed<Frac>> {
                    let (round, overflow) = self.overflowing_round();
                    if overflow { None } else { Some(round) }
                }
            }

            doc_comment! {
                concat!(r#"
Saturating ceil. Rounds to the next integer towards +∞, saturating on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_ceil(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).saturating_ceil(), Fix::from_int(-2));"#, ""
), r#"
assert_eq!(Fix::max_value().saturating_ceil(), Fix::max_value());
```
"#,
                ),
                #[inline]
                pub fn saturating_ceil(self) -> $Fixed<Frac> {
                    let saturated = $Fixed::max_value();
                    let (ceil, overflow) = self.overflowing_ceil();
                    if overflow { saturated } else { ceil }
                }
            }

            doc_comment! {
                concat!(if_signed_unsigned!($Signedness, r#"
Saturating floor. Rounds to the next integer towards −∞, saturating on overflow.

Overflow can only occur when there are zero integer bits.
"#, r#"
Saturating floor. Rounds to the next integer towards −∞.
Cannot overflow for unsigned values.
"#), r#"

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_floor(), Fix::from_int(2));"#,
if_signed_unsigned!($Signedness, concat!(r#"
assert_eq!((-two_half).saturating_floor(), Fix::from_int(-3));
type AllFrac = "#, stringify!($Fixed), "<frac::", stringify!($Len), r#">;
assert_eq!(AllFrac::min_value().saturating_floor(), AllFrac::min_value());"#), ""
), r#"
```
"#,
                ),
                #[inline]
                pub fn saturating_floor(self) -> $Fixed<Frac> {
                    let saturated = $Fixed::min_value();
                    let (floor, overflow) = self.overflowing_floor();
                    if overflow { saturated } else { floor }
                }
            }

            doc_comment! {
                concat!(r#"
Saturating round. Rounds to the nearest integer, with ties rounded away from
zero, and saturating on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_round(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).saturating_round(), Fix::from_int(-3));"#, ""
), r#"
assert_eq!(Fix::max_value().saturating_round(), Fix::max_value());
```
"#,
                ),
                #[inline]
                pub fn saturating_round(self) -> $Fixed<Frac> {
                    let saturated = if self.to_bits() > 0 {
                        $Fixed::max_value()
                    } else {
                        $Fixed::min_value()
                    };
                    let (round, overflow) = self.overflowing_round();
                    if overflow { saturated } else { round }
                }
            }

            doc_comment! {
                concat!(r#"
Wrapping ceil. Rounds to the next integer towards +∞, wrapping on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_ceil(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).wrapping_ceil(), Fix::from_int(-2));"#, ""
), r#"
assert_eq!(Fix::max_value().wrapping_ceil(), Fix::min_value());
```
"#,
                ),
                #[inline]
                pub fn wrapping_ceil(self) -> $Fixed<Frac> {
                    self.overflowing_ceil().0
                }
            }

            doc_comment! {
                concat!(if_signed_unsigned!($Signedness, r#"
Wrapping floor. Rounds to the next integer towards −∞, wrapping on overflow.

Overflow can only occur when there are zero integer bits.
"#, r#"
Wrapping floor. Rounds to the next integer towards −∞.
Cannot overflow for unsigned values.
"#), r#"

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_floor(), Fix::from_int(2));"#,
if_signed_unsigned!($Signedness, concat!(r#"
assert_eq!((-two_half).wrapping_floor(), Fix::from_int(-3));
type AllFrac = "#, stringify!($Fixed), "<frac::", stringify!($Len), r#">;
assert_eq!(AllFrac::min_value().wrapping_floor(), AllFrac::from_int(0));"#), ""
), r#"
```
"#,
                ),
                #[inline]
                pub fn wrapping_floor(self) -> $Fixed<Frac> {
                    self.overflowing_floor().0
                }
            }

            doc_comment! {
                concat!(r#"

Wrapping round. Rounds to the next integer to the nearest, with ties
rounded away from zero, and wrapping on overflow.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_round(), Fix::from_int(3));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).wrapping_round(), Fix::from_int(-3));"#, ""
), r#"
assert_eq!(Fix::max_value().wrapping_round(), Fix::min_value());
```
"#,
                ),
                #[inline]
                pub fn wrapping_round(self) -> $Fixed<Frac> {
                    self.overflowing_round().0
                }
            }

            doc_comment! {
                concat!(r#"
Overflowing ceil. Rounds to the next integer towards +∞.

Returns a tuple of the fixed-point number and a [`bool`], indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_ceil(), (Fix::from_int(3), false));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).overflowing_ceil(), (Fix::from_int(-2), false));"#, ""
), r#"
assert_eq!(Fix::max_value().overflowing_ceil(), (Fix::min_value(), true));
```
"#,
                ),
                #[inline]
                pub fn overflowing_ceil(self) -> ($Fixed<Frac>, bool) {
                    let int = self.int();
                    if self.frac() == 0 {
                        return (int, false);
                    }
                    if Self::int_bits() == 0 {
                        return (int, self.to_bits() > 0);
                    }
                    let increment = Self::from_bits(<Self as SealedFixed>::lowest_int_bit());
                        if_signed! {
                            $Signedness;
                            if Self::int_bits() == 1 {
                                return int.overflowing_sub(increment);
                            }
                        }
                        int.overflowing_add(increment)
                    }
            }

            doc_comment! {
                concat!(r#"
Overflowing floor. Rounds to the next integer towards −∞.

"#, if_signed_unsigned!($Signedness, r#"
Returns a tuple of the fixed-point number and a [`bool`], indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned. Overflow can only occur when there are zero integer bits.
"#, r#"
Returns a tuple of the fixed-point number and [`false`][`bool`].
"#), r#"

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_floor(), (Fix::from_int(2), false));"#,
if_signed_unsigned!($Signedness, concat!(r#"
assert_eq!((-two_half).overflowing_floor(), (Fix::from_int(-3), false));
type AllFrac = "#, stringify!($Fixed), "<frac::", stringify!($Len), r#">;
assert_eq!(AllFrac::min_value().overflowing_floor(), (AllFrac::from_int(0), true));"#), ""
), r#"
```
"#,
                ),
                #[inline]
                pub fn overflowing_floor(self) -> ($Fixed<Frac>, bool) {
                    let int = self.int();
                    if_signed! {
                        $Signedness;
                        if Self::int_bits() == 0 {
                            return (int, self.to_bits() < 0);
                        }
                    }
                    (int, false)
                }
            }

            doc_comment! {
                concat!(r#"
Overflowing round. Rounds to the next integer to the nearest,
with ties rounded away from zero.

Returns a tuple of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
use fixed::frac;
use fixed::"#, stringify!($Fixed), r#";
type Fix = "#, stringify!($Fixed), r#"<frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_round(), (Fix::from_int(3), false));"#,
if_signed_unsigned!($Signedness, r#"
assert_eq!((-two_half).overflowing_round(), (Fix::from_int(-3), false));"#, ""
), r#"
assert_eq!(Fix::max_value().overflowing_round(), (Fix::min_value(), true));
```
"#,
                ),
                #[inline]
                pub fn overflowing_round(self) -> ($Fixed<Frac>, bool) {
                    let int = self.int();
                    let highest_frac_bit = <Self as SealedFixed>::highest_frac_bit();
                    if (self.to_bits() & highest_frac_bit) == 0 {
                        return (int, false);
                    }
                    let increment = Self::from_bits(<Self as SealedFixed>::lowest_int_bit());
                    if_signed! {
                        $Signedness;
                        let tie = self.frac().to_bits() == highest_frac_bit;
                        if Self::int_bits() == 0 {
                            // if num is .100...00 = -0.5, we have overflow
                            // otherwise .100...01, 0 < x < -0.5,  no overflow
                            return (int, tie);
                        }
                        // If num is −int.100...00 = (-int) + 0.5, we simply truncate to move to −∞.
                        // If num is −int.100...01 = (-int) + 0.6, we add 1 to −int.
                        // If num is +int.100...00 = (+int) + 0.5, we add 1 to +int.
                        // If num is +int.100...01 = (+int) + 0.6, we add 1 to +int.
                        if tie && self.to_bits() < 0 {
                            return (int, false);
                        }
                        if Self::int_bits() == 1 {
                            return int.overflowing_sub(increment);
                        }
                        int.overflowing_add(increment)
                    }
                    if_unsigned! {
                        $Signedness;
                        if Self::int_bits() == 0 {
                            return (int, true);
                        }
                        int.overflowing_add(increment)
                    }
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
                    "```\n",
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
                    "```\n",
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
                    "assert_eq!(f.leading_zeros(), ", stringify!($nbits), " - 6);\n",
                    "```\n",
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
                    "```\n",
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
                    "let bits: ", stringify!($Inner), " = (0b111 << (", stringify!($nbits), " - 3)) | 0b1010;\n",
                    "let rot = 0b1010111;\n",
                    "assert_eq!(bits.rotate_left(3), rot);\n",
                    "assert_eq!(Fix::from_bits(bits).rotate_left(3), Fix::from_bits(rot));\n",
                    "```\n",
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
                    "let rot = (0b111 << (", stringify!($nbits), " - 3)) | 0b1010;\n",
                    "assert_eq!(bits.rotate_right(3), rot);\n",
                    "assert_eq!(Fix::from_bits(bits).rotate_right(3), Fix::from_bits(rot));\n",
                    "```\n",
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
                $Signedness;
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
                $Signedness;
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
                $Signedness;
                /// Overflowing absolute value.
                #[inline]
                pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = <$Inner>::overflowing_abs(self.to_bits());
                    ($Fixed::from_bits(ans), o)
                }
            }

            if_unsigned! {
                $Signedness;
                pass_method! {
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
                        "```\n",
                    ),
                    $Fixed($Inner) => fn is_power_of_two(self) -> bool
                }
            }

            if_unsigned! {
                $Signedness;
                pass_method! {
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
                        "```\n",
                    ),
                    $Fixed($Inner) => fn next_power_of_two(self)
                }
            }

            if_unsigned! {
                $Signedness;
                doc_comment! {
                    concat!(
                        "Returns the smallest power of two ≥ `self`, or [`None`]\n",
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
                        "```\n",
                        "\n",
                        "[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None\n",
                    ),
                    #[inline]
                    pub fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                        <$Inner>::checked_next_power_of_two(self.to_bits()).map($Fixed::from_bits)
                    }
                }
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "Returns the absolute value.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "let five = Fix::from_int(5);\n",
                        "let minus_five = Fix::from_int(-5);\n",
                        "assert_eq!(five.abs(), five);\n",
                        "assert_eq!(minus_five.abs(), five);\n",
                        "```\n",
                    ),
                    $Fixed($Inner) => fn abs(self)
                }
            }

            if_signed! {
                $Signedness;
                doc_comment! {
                    concat!(
                        "Returns a number representing the sign of `self`.\n",
                        "\n",
                        "# Panics\n",
                        "\n",
                        "This method panics:\n",
                        "  * if the value is positive and the fixed-point number has zero\n",
                        "    or one integer bits such that it cannot hold the value 1.\n",
                        "  * if the value is negative and the fixed-point number has zero\n",
                        "    integer bits, such that it cannot hold the value −1.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert_eq!(Fix::from_int(5).signum(), 1);\n",
                        "assert_eq!(Fix::from_int(0).signum(), 0);\n",
                        "assert_eq!(Fix::from_int(-5).signum(), -1);\n",
                        "```\n",
                    ),
                    #[inline]
                    pub fn signum(self) -> $Fixed<Frac> {
                        match self.to_bits().cmp(&0) {
                            Ordering::Equal => $Fixed::from_bits(0),
                            Ordering::Greater => {
                                <$Fixed<Frac> as SealedFixed>::one().expect("overflow")
                            }
                            Ordering::Less => {
                                <$Fixed<Frac> as SealedFixed>::minus_one().expect("overflow")
                            }
                        }
                    }
                }
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "Returns `true` if the number is > 0.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert!(Fix::from_int(5).is_positive());\n",
                        "assert!(!Fix::from_int(0).is_positive());\n",
                        "assert!(!Fix::from_int(-5).is_positive());\n",
                        "```\n",
                    ),
                    $Fixed($Inner) => fn is_positive(self) -> bool
                }
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "Returns `true` if the number is < 0.\n",
                        "\n",
                        "# Examples\n",
                        "\n",
                        "```rust\n",
                        "use fixed::frac;\n",
                        "use fixed::", stringify!($Fixed), ";\n",
                        "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                        "assert!(!Fix::from_int(5).is_negative());\n",
                        "assert!(!Fix::from_int(0).is_negative());\n",
                        "assert!(Fix::from_int(-5).is_negative());\n",
                        "```\n",
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

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::cyclomatic_complexity))]
    #[allow(deprecated)]
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
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), true));

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), false));

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), false));

        type U0F32 = FixedU32<U32>;

        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), false));

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), true));

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), true));

        type I16F16 = FixedI32<U16>;

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_int(), -4);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-4), false));

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_int(), -4);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-4), false));

        // -3.5 + Δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_int(), -4);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-3), false));

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_int(), -1);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-1), false));

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_int(), -1);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-1), false));

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_int(), -1);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(0), false));

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(0), false));

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(1), false));

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(1), false));

        // 3.5 - Δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(3), false));

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(4), false));

        // 3.5 + Δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(4), false));

        type U16F16 = FixedU32<U16>;

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(0), false));

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(1), false));

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(1), false));

        // 3.5 - Δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(3), false));

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(4), false));

        // 3.5 + Δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(4), false));
    }
}
