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

## Quick examples

```rust
// 20 integer bits, 12 fractional bits
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// find the ceil and convert to i32
assert_eq!(six_and_third.ceil().to_int::<i32>(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
[`FixedI32<frac::U12>`][`FixedI32`]. The unsigned counterpart would be
[`U20F12`]. Aliases are provided for all combinations of integer and
fractional bits adding up to a total of eight, 16, 32, 64 or 128 bits.

```rust
// −8 ≤ I4F4 < 8 with steps of 1/16 (about 0.06)
use fixed::types::I4F4;
let a = I4F4::from_int(1);
// multiplication and division by integers is possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (3.19)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.19");

// −8 ≤ I4F12 < 8 with steps of 1/4096 (about 0.0002)
use fixed::types::I4F12;
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_fixed(wider_ans);
// now the answer is the much closer 3 6/16 (3.38)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.38");
```

The second example shows some precision and conversion issues. The low
precision of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to
an inaccurate result `ans1` = 3 3⁄16 (3.19). With a higher precision,
we get `wider_a / 5` equal to 819⁄4096, leading to a more accurate
intermediate result `wider_ans` = 3 1635⁄4096. When we convert back to
four fractional bits, we get `ans2` = 3 6⁄16 (3.38).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as
the target type has the same number of integer bits and a larger
number of fractional bits. Converting from [`I4F12`] to [`I4F4`]
cannot use [`From`] as we have less fractional bits, so we use
[`from_fixed`] instead.

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.2.1"
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
version = "0.2.1"
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
[`I4F12`]: types/type.I4F12.html
[`I4F4`]: types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`U20F12`]: types/type.U20F12.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_fixed`]: struct.FixedI8.html#method.from_fixed
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.2.1")]
#![doc(test(attr(deny(warnings))))]
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
macro_rules! if_signed_else_empty_str {
    (Signed, $($signed:tt)*) => {
        concat!($($signed)*)
    };
    (Unsigned, $($signed:tt)*) => {
        ""
    };
}
// macro_rules! if_unsigned_else_empty_str {
//     (Signed, $($unsigned:tt)*) => {
//         ""
//     };
//     (Unsigned, $($unsigned:tt)*) => {
//         concat!($($unsigned)*)
//     };
// }

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
use sealed::{Fixed, Float, Int, SealedFixed, SealedFloat, SealedInt, Widest};

macro_rules! pass_method {
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident()) => {
        #[doc = $comment]
        #[inline]
        pub fn $method() -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::$method())
        }
    };
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident(self)) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self) -> $Fixed<Frac> {
            Self::from_bits(<$Inner>::$method(self.to_bits()))
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
            Self::from_bits(<$Inner>::$method(self.to_bits(), $param))
        }
    };
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! deprecated_from_float {
    (fn $method:ident($Float:ident) -> $Fixed:ident<$Frac:ident>) => {
        doc_comment!(
            concat!(
                "Creates a fixed-point number from `",
                stringify!($Float),
                "`.

This method has been replaced by [`checked_from_float`].

[`checked_from_float`]: #method.checked_from_float
"
            ),
            #[deprecated(since = "0.2.0", note = "replaced by checked_from_float")]
            #[inline]
            pub fn $method(val: $Float) -> Option<$Fixed<$Frac>> {
                Self::checked_from_float(val)
            }
        );
    };
}

macro_rules! deprecated_to_float {
    (fn $method:ident($Fixed:ident) -> $Float:ident) => {
        doc_comment!(
            concat!(
                "Converts the fixed-point number to `",
                stringify!($Float),
                "`.

This method has been replaced by [`to_float`].

[`to_float`]: #method.to_float
"
            ),
            #[deprecated(since = "0.2.0", note = "replaced by to_float")]
            #[inline]
            pub fn $method(self) -> $Float {
                self.to_float()
            }
        );
    };
}

macro_rules! fixed {
    ($description:expr, $Fixed:ident($Inner:ty, $Len:tt, $nbits:expr), $Signedness:tt) => {
        doc_comment!(
            concat!(
                $description,
                "with `Frac` fractional bits.

Currently `Frac` is an [`Unsigned`] as provided by the
[typenum crate]; it is planned to move to [const generics] when they
are implemented by the Rust compiler.

# Examples

```rust
use fixed::frac::U3;
use fixed::",
                stringify!($Fixed),
                ";
let eleven = ",
                stringify!($Fixed),
                "::<U3>::from_bits(11 << 3);
let five_half = eleven >> 1u32;
assert_eq!(eleven.to_string(), \"11.0\");
assert_eq!(five_half.to_string(), \"5.5\");
```

[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
[typenum crate]: https://crates.io/crates/typenum
",
            ),
            #[repr(transparent)]
            pub struct $Fixed<Frac>(($Inner, PhantomData<Frac>))
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>;
        );

        impl<Frac> Clone for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            #[inline]
            fn clone(&self) -> $Fixed<Frac> {
                Self::from_bits(self.to_bits())
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
                Self::from_bits(<$Inner>::default())
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
            pass_method! {
                concat!(
                    "Returns the smallest value that can be
represented.

# Examples

```rust
type Fix = fixed::", stringify!($Fixed), "<fixed::frac::U4>;
assert_eq!(Fix::min_value(), Fix::from_bits(",
                    stringify!($Inner),
                    "::min_value()));
```
",
                ),
                $Fixed($Inner) => fn min_value()
            }
            pass_method! {
                concat!(
                    "Returns the largest value that can be
represented.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::max_value(), Fix::from_bits(",
                    stringify!($Inner),
                    "::max_value()));
```
",
                ),
                $Fixed($Inner) => fn max_value()
            }

            doc_comment!(
                concat!(
                    "Returns the number of integer bits.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
assert_eq!(Fix::int_bits(), ",
                    stringify!($nbits),
                    " - 6);
```
"
                ),
                #[inline]
                pub fn int_bits() -> u32 {
                    Self::INT_NBITS
                }
            );

            doc_comment!(
                concat!(
                    "Returns the number of fractional bits.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
assert_eq!(Fix::frac_bits(), 6);
```
",
                ),
                #[inline]
                pub fn frac_bits() -> u32 {
                    Self::FRAC_NBITS
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number that has a bitwise
representation identical to the given integer.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 0010.0000 == 2
assert_eq!(Fix::from_bits(0b10_0000), 2);
```
",
                ),
                #[inline]
                pub fn from_bits(v: $Inner) -> $Fixed<Frac> {
                    $Fixed((v, PhantomData))
                }
            );

            doc_comment!(
                concat!(
                    "Creates an integer that has a bitwise
representation identical to the given fixed-point number.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 2 is 0010.0000
assert_eq!(Fix::from_int(2).to_bits(), 0b10_0000);
```
",
                ),
                #[inline]
                pub fn to_bits(self) -> $Inner {
                    (self.0).0
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from another
fixed-point number which can have a different type.

Any extra fractional bits are truncated.

# Panics

In debug mode, panics if the value does not fit. In release mode the
value is wrapped, but it is not considered a breaking change if in the
future it panics; if wrapping is required use [`wrapping_from_fixed`]
instead.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::from_fixed(src), Dst::from_bits(0b111 << (4 - 2)));
// src >> 4 is 0.000111, which for Dst is truncated to 0.0001
assert_eq!(Dst::from_fixed(src >> 4), Dst::from_bits(1));
```

[`wrapping_from_fixed`]: #method.wrapping_from_fixed
",
                ),
                #[inline]
                pub fn from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    let (wrapped, overflow) = Self::overflowing_from_fixed(val);
                    debug_assert!(!overflow, "{} overflows", val);
                    let _ = overflow;
                    wrapped
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to another
fixed-point number which can have a different type.

Any extra fractional bits are truncated.

# Panics

In debug mode, panics if the value does not fit. In release mode the
value is wrapped, but it is not considered a breaking change if in the
future it panics; if wrapping is required use [`wrapping_to_fixed`]
instead.

# Examples

```rust
type Src = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
type Dst = fixed::FixedI32<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (6 - 2));
assert_eq!(src.to_fixed::<Dst>(), Dst::from_bits(0b111 << (4 - 2)));
// src >> 4 is 0.000111, which for Dst is truncated to 0.0001
assert_eq!((src >> 4u32).to_fixed::<Dst>(), Dst::from_bits(1));
```

[`wrapping_to_fixed`]: #method.wrapping_to_fixed
",
                ),
                #[inline]
                pub fn to_fixed<F>(self) -> F
                where
                    F: Fixed,
                {
                    let (wrapped, overflow) = F::overflowing_from_fixed(self);
                    debug_assert!(!overflow, "{} overflows", self);
                    let _ = overflow;
                    wrapped
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from an integer.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

# Panics

In debug mode, panics if the value does not fit. In release mode the
value is wrapped, but it is not considered a breaking change if in the
future it panics; if wrapping is required use [`wrapping_from_int`]
instead.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::from_int(3i32), Fix::from_bits(3 << 4));
assert_eq!(Fix::from_int(",
                    if_signed_unsigned!(
                        $Signedness,
                        "-3i64), Fix::from_bits(-",
                        "3i64), Fix::from_bits(",
                    ),
                    "3 << 4));
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`wrapping_from_int`]: #method.wrapping_from_int
",
                ),
                #[inline]
                pub fn from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    let (wrapped, overflow) = Self::overflowing_from_int(val);
                    debug_assert!(!overflow, "{} overflows", val);
                    let _ = overflow;
                    wrapped
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number of type to an integer.

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

Any fractional bits are truncated.

# Panics

In debug mode, panics if the value does not fit. In release mode the
value is wrapped, but it is not considered a breaking change if in the
future it panics; if wrapping is required use [`wrapping_to_int`]
instead.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.to_int::<i32>(), 2);
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        "(-two_point_5).to_int::<i64>(), -3",
                        "two_point_5.to_int::<i64>(), 2",
                    ),
                    ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`wrapping_to_int`]: #method.wrapping_to_int
",
                ),
                #[inline]
                pub fn to_int<I>(self) -> I
                where
                    I: Int,
                {
                    let (wrapped, overflow) = <I as SealedInt>::overflowing_from_fixed(self);
                    debug_assert!(!overflow, "{} overflows", self);
                    let _ = overflow;
                    wrapped
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from a
floating-point number.

The floating-point number can be of type [`f32`] or [`f64`]. If the
[`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

Panics if the value is not [finite].

In debug mode, also panics if the value does not fit. In release mode
the value is wrapped, but it is not considered a breaking change if in
the future it panics; if wrapping is required use
[`wrapping_from_float`] instead.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
assert_eq!(Fix::from_float(1.75f32), Fix::from_bits(0b111 << (4 - 2)));
assert_eq!(Fix::from_float(",
                    if_signed_unsigned!(
                        $Signedness,
                        "-1.75f64), Fix::from_bits(-",
                        "1.75f64), Fix::from_bits(",
                    ),
                    "0b111 << (4-2)));
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`wrapping_from_float`]: #method.wrapping_from_float
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
",
                ),
                #[inline]
                pub fn from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    let (wrapped, overflow) = Self::overflowing_from_float(val);
                    debug_assert!(!overflow, "{} overflows", val);
                    let _ = overflow;
                    wrapped
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to a floating-point
number.

The floating-point number can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.625 is 1.101 in binary
assert_eq!(Fix::from_bits(0b1101 << (4 - 3)).to_float::<f32>(), 1.625f32);
assert_eq!(Fix::from_bits(",
                    if_signed_unsigned!(
                        $Signedness,
                        "-0b1101 << (4 - 3)).to_float::<f64>(), -",
                        "0b1101 << (4 - 3)).to_float::<f64>(), "
                    ),
                    "1.625f64);
let max_fixed = fixed::FixedU128::<fixed::frac::U0>::max_value();
assert_eq!(max_fixed.to_float::<f32>(), std::f32::INFINITY);
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
",
                ),
                pub fn to_float<F>(self) -> F
                where
                    F: Float,
                {
                    let (neg, abs) = self.to_bits().neg_abs();
                    SealedFloat::from_neg_abs(
                        neg,
                        u128::from(abs),
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    )
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from another
fixed-point number if it fits, otherwise returns [`None`].

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::checked_from_fixed(src), Some(Dst::from_bits(0b111 << (4 - 2))));
let too_large = fixed::",
                    stringify!($Fixed),
                    "::<fixed::frac::U2>::max_value();
assert!(Dst::checked_from_fixed(too_large).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
",
                ),
                #[inline]
                pub fn checked_from_fixed<F>(val: F) -> Option<$Fixed<Frac>>
                where
                    F: Fixed,
                {
                    let (wrapped, overflow) = Self::overflowing_from_fixed(val);
                    if overflow { None } else { Some(wrapped) }
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to another
fixed-point number if it fits, otherwise returns [`None`].

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(src.checked_to_fixed::<Dst>(), Some(expected));
type TooFewIntBits = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
assert!(Src::max_value().checked_to_fixed::<TooFewIntBits>().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
",
                ),
                #[inline]
                pub fn checked_to_fixed<F>(self) -> Option<F>
                where
                    F: Fixed,
                {
                    match F::overflowing_from_fixed(self) {
                        (wrapped, false) => Some(wrapped),
                        (_, true) => None,
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from an integer if
it fits, otherwise returns [`None`].

The integer can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::checked_from_int(3), Some(Fix::from_bits(3 << 4)));
let too_large = ",
                    stringify!($Inner),
                    "::max_value();
assert!(Fix::checked_from_int(too_large).is_none());
let too_small = ",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(stringify!($Inner), "::min_value()"),
                        "-1",
                    ),
                    ";
assert!(Fix::checked_from_int(too_small).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn checked_from_int<I>(val: I) -> Option<$Fixed<Frac>>
                where
                    I: Int,
                {
                    let (wrapped, overflow) = Self::overflowing_from_int(val);
                    if overflow { None } else { Some(wrapped) }
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to an integer if it
fits, otherwise returns [`None`].

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.checked_to_int::<i32>(), Some(2));
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        "(-two_point_5).checked_to_int::<i64>(), Some(-3",
                        "two_point_5.checked_to_int::<i64>(), Some(2",
                    ),
                    "));
type AllInt = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U0>;
assert!(AllInt::",
                    if_signed_unsigned!(
                        $Signedness,
                        "from_bits(-1).checked_to_int::<u",
                        "max_value().checked_to_int::<i",
                    ),
                    stringify!($nbits),
                    ">().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn checked_to_int<I>(self) -> Option<I>
                where
                    I: Int,
                {
                    match <I as SealedInt>::overflowing_from_fixed(self) {
                        (wrapped, false) => Some(wrapped),
                        (_, true) => None,
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from a
floating-point number if it fits, otherwise returns [`None`].

The floating-point number can be of type [`f32`] or [`f64`]. If the
[`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let expected = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::checked_from_float(1.75f32), Some(expected));
assert_eq!(Fix::checked_from_float(",
                    if_signed_unsigned!(
                        $Signedness,
                        "-1.75f64), Some(-",
                        "1.75f64), Some(",
                    ),
                    "expected));
assert!(Fix::checked_from_float(2e38).is_none());
assert!(Fix::checked_from_float(std::f64::NAN).is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
",
                ),
                #[inline]
                pub fn checked_from_float<F>(val: F) -> Option<$Fixed<Frac>>
                where
                    F: Float,
                {
                    if !val.is_finite() {
                        return None;
                    }
                    let (wrapped, overflow) = Self::overflowing_from_float(val);
                    if overflow { None } else { Some(wrapped) }
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from another
fixed-point number, saturating the value if it does not fit.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::saturating_from_fixed(src), Dst::from_bits(0b111 << (4 - 2)));
let too_large = fixed::",
                    stringify!($Fixed),
                    "::<fixed::frac::U2>::max_value();
assert_eq!(Dst::saturating_from_fixed(too_large), Dst::max_value());
let too_small = ",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!("fixed::", stringify!($Fixed), "::<fixed::frac::U2>::min_value()"),
                        "Src::from_bits(-1)"
                    ),
                    ";
assert_eq!(Dst::saturating_from_fixed(too_small), Dst::min_value());
```
",
                ),
                #[inline]
                pub fn saturating_from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    let (value, _, overflow) = val.to_bits().to_fixed_dir_overflow(
                        F::FRAC_NBITS as i32,
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    if overflow {
                        return if val.to_bits().is_negative() {
                            Self::min_value()
                        } else {
                            Self::max_value()
                        };
                    }
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    return Self::max_value();
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(_) => return Self::min_value(),
                        },
                    );
                    SealedFixed::from_bits(bits)
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to another
fixed-point number, saturating the value if it does not fit.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
assert_eq!(src.saturating_to_fixed::<Dst>(), Dst::from_bits(0b111 << (16 - 2)));
type TooFewIntBits = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
let saturated = Src::max_value().saturating_to_fixed::<TooFewIntBits>();
assert_eq!(saturated, TooFewIntBits::max_value());
```
",
                ),
                #[inline]
                pub fn saturating_to_fixed<F>(self) -> F
                where
                    F: Fixed,
                {
                    match F::overflowing_from_fixed(self) {
                        (wrapped, false) => wrapped,
                        (_, true) => {
                            if self.to_bits().is_negative() {
                                F::from_bits(F::Bits::min_value())
                            } else {
                                F::from_bits(F::Bits::max_value())
                            }
                        }
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from an integer,
saturating the value if it does not fit.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::saturating_from_int(3), Fix::from_bits(3 << 4));
let too_large = ",
                    stringify!($Inner),
                    "::max_value();
assert_eq!(Fix::saturating_from_int(too_large), Fix::max_value());
let too_small = ",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(stringify!($Inner), "::min_value()"),
                        "-1",
                    ),
                    ";
assert_eq!(Fix::saturating_from_int(too_small), Fix::min_value());
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn saturating_from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    let (value, _, overflow) = val.to_fixed_dir_overflow(
                        0,
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    if overflow {
                        return if val.is_negative() {
                            Self::min_value()
                        } else {
                            Self::max_value()
                        };
                    }
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    return Self::max_value();
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(_) => return Self::min_value(),
                        },
                    );
                    SealedFixed::from_bits(bits)
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to an integer,
saturating the value if it does not fit.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.saturating_to_int::<i32>(), 2);
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        "(-two_point_5).saturating_to_int::<i64>(), -3",
                        "two_point_5.saturating_to_int::<i64>(), 2",
                    ),
                    ");
type AllInt = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U0>;
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "AllInt::from_bits(-1).saturating_to_int::<u",
                            stringify!($nbits),
                            ">(), 0",
                        ),
                        concat!(
                            "AllInt::max_value().saturating_to_int::<i",
                            stringify!($nbits),
                            ">(), i",
                            stringify!($nbits),
                            "::max_value()",
                        ),
                    ),
                    ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn saturating_to_int<I>(self) -> I
                where
                    I: Int,
                {
                    match <I as SealedInt>::overflowing_from_fixed(self) {
                        (wrapped, false) => wrapped,
                        (_, true) => {
                            if self.to_bits().is_negative() {
                                I::min_value()
                            } else {
                                I::max_value()
                            }
                        }
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from a
floating-point number, saturating the value if it does not fit.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is [NaN].

# Examples

```rust
use std::f64;
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.625 is 1.101 in binary
let one_point_625 = Fix::from_bits(0b1101 << (4 - 3));
assert_eq!(Fix::saturating_from_float(1.625f32), one_point_625);
assert_eq!(Fix::saturating_from_float(2e38), Fix::max_value());
assert_eq!(Fix::saturating_from_float(f64::NEG_INFINITY), Fix::min_value());
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[NaN]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_nan
",
                ),
                #[inline]
                pub fn saturating_from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    assert!(!val.is_nan(), "NaN");
                    let saturated = if val.is_sign_negative() {
                        Self::min_value()
                    } else {
                        Self::max_value()
                    };
                    if !val.is_finite() {
                        return saturated;
                    }
                    let (value, _, overflow) = val.to_fixed_dir_overflow(
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    if overflow {
                        return saturated;
                    }
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    return Self::max_value();
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(_) => return Self::min_value(),
                        },
                    );
                    SealedFixed::from_bits(bits)
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from another
fixed-point number, wrapping the value on overflow.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
let expected = Dst::from_bits(0b111 << (4 - 2));
assert_eq!(Dst::wrapping_from_fixed(src), expected);
// integer 0b1101 << (",
                    stringify!($nbits),
                    " - 7) will wrap to fixed-point 1010...
let too_large = fixed::",
                    stringify!($Fixed),
                    "::<fixed::frac::U0>::from_bits(0b1101 << (",
                    stringify!($nbits),
                    " - 7));
let wrapped = Dst::from_bits(0b1010 << (", stringify!($nbits), " - 4));
assert_eq!(Dst::wrapping_from_fixed(too_large), wrapped);
```
",
                ),
                #[inline]
                pub fn wrapping_from_fixed<F>(val: F) -> $Fixed<Frac>
                where
                    F: Fixed,
                {
                    Self::overflowing_from_fixed(val).0
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to another
fixed-point number, wrapping the value on overflow.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::wrapping_from_fixed(src), expected);
type TooFewIntBits = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
let wrapped = TooFewIntBits::from_bits(Src::max_value().to_bits() << 2);
assert_eq!(Src::max_value().wrapping_to_fixed::<TooFewIntBits>(), wrapped);
```
",
                ),
                #[inline]
                pub fn wrapping_to_fixed<F>(self) -> F
                where
                    F: Fixed,
                {
                    F::overflowing_from_fixed(self).0
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from an integer,
wrapping the value on overflow.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::wrapping_from_int(3), Fix::from_bits(3 << 4));
// integer 0b1101 << (",
                    stringify!($nbits),
                    " - 7) will wrap to fixed-point 1010...
let large: ",
                    stringify!($Inner),
                    " = 0b1101 << (",
                    stringify!($nbits),
                    " - 7);
let wrapped = Fix::from_bits(0b1010 << (",
                    stringify!($nbits),
                    " - 4));
assert_eq!(Fix::wrapping_from_int(large), wrapped);
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn wrapping_from_int<I>(val: I) -> $Fixed<Frac>
                where
                    I: Int,
                {
                    Self::overflowing_from_int(val).0
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to an integer,
wrapping the value on overflow.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.wrapping_to_int::<i32>(), 2);
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        "(-two_point_5).wrapping_to_int::<i64>(), -3",
                        "two_point_5.wrapping_to_int::<i64>(), 2",
                    ),
                    ");
type AllInt = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U0>;
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!(
                            "AllInt::from_bits(-1).wrapping_to_int::<u",
                            stringify!($nbits),
                            ">(), u",
                            stringify!($nbits),
                            "::max_value()",
                        ),
                        concat!(
                            "AllInt::max_value().wrapping_to_int::<i",
                            stringify!($nbits),
                            ">(), -1",
                        ),
                    ),
                    ");
```

[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn wrapping_to_int<I>(self) -> I
                where
                    I: Int,
                {
                    <I as SealedInt>::overflowing_from_fixed(self).0
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from a
floating-point number, wrapping the value on overflow.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is not [finite].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let from_bits = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::wrapping_from_float(1.75f32), from_bits);
assert_eq!(Fix::wrapping_from_float(",
                    if_signed_unsigned!($Signedness, "-1.75f64), -", "1.75f64), "),
                    "from_bits);
// 1.75 << (",
                    stringify!($nbits),
                    " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(",
                    stringify!($nbits),
                    " - 4);
let wrapped = Fix::from_bits(0b1100 << (",
                    stringify!($nbits),
                    " - 4));
assert_eq!(Fix::wrapping_from_float(large), wrapped);
```

[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
",
                ),
                #[inline]
                pub fn wrapping_from_float<F>(val: F) -> $Fixed<Frac>
                where
                    F: Float,
                {
                    Self::overflowing_from_float(val).0
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from another
fixed-point number.

Returns a tuple of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::FixedI32<fixed::frac::U16>;
type Dst = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (16 - 2));
let expected = Dst::from_bits(0b111 << (4 - 2));
assert_eq!(Dst::overflowing_from_fixed(src), (expected, false));
// integer 0b1101 << (",
                    stringify!($nbits),
                    " - 7) will wrap to fixed-point 1010...
let too_large = fixed::",
                    stringify!($Fixed),
                    "::<fixed::frac::U0>::from_bits(0b1101 << (",
                    stringify!($nbits),
                    " - 7));
let wrapped = Dst::from_bits(0b1010 << (", stringify!($nbits), " - 4));
assert_eq!(Dst::overflowing_from_fixed(too_large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
",
                ),
                #[inline]
                pub fn overflowing_from_fixed<F>(val: F) -> ($Fixed<Frac>, bool)
                where
                    F: Fixed,
                {
                    let (value, _, mut overflow) = val.to_bits().to_fixed_dir_overflow(
                        F::FRAC_NBITS as i32,
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    overflow = true;
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(bits) => {
                                overflow = true;
                                bits as <Self as SealedFixed>::Bits
                            }
                        },
                    );
                    (SealedFixed::from_bits(bits), overflow)
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to another
fixed-point number.

Returns a tuple of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Any extra fractional bits are truncated.

# Examples

```rust
type Src = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
type Dst = fixed::FixedI32<fixed::frac::U16>;
// 1.75 is 1.11 in binary
let src = Src::from_bits(0b111 << (4 - 2));
let expected = Dst::from_bits(0b111 << (16 - 2));
assert_eq!(Dst::overflowing_from_fixed(src), (expected, false));
type TooFewIntBits = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U6>;
let wrapped = TooFewIntBits::from_bits(Src::max_value().to_bits() << 2);
assert_eq!(Src::max_value().overflowing_to_fixed::<TooFewIntBits>(), (wrapped, true));
```
",
                ),
                #[inline]
                pub fn overflowing_to_fixed<F>(self) -> (F, bool)
                where
                    F: Fixed,
                {
                    F::overflowing_from_fixed(self)
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from an integer.

Returns a tuple of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
assert_eq!(Fix::overflowing_from_int(3), (Fix::from_bits(3 << 4), false));
// integer 0b1101 << (",
                    stringify!($nbits),
                    " - 7) will wrap to fixed-point 1010...
let large: ",
                    stringify!($Inner),
                    " = 0b1101 << (",
                    stringify!($nbits),
                    " - 7);
let wrapped = Fix::from_bits(0b1010 << (",
                    stringify!($nbits),
                    " - 4));
assert_eq!(Fix::overflowing_from_int(large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn overflowing_from_int<I>(val: I) -> ($Fixed<Frac>, bool)
                where
                    I: Int,
                {
                    let (value, _, mut overflow) = val.to_fixed_dir_overflow(
                        0,
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    overflow = true;
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(bits) => {
                                overflow = true;
                                bits as <Self as SealedFixed>::Bits
                            }
                        },
                    );
                    (SealedFixed::from_bits(bits), overflow)
                }
            );

            doc_comment!(
                concat!(
                    "Converts a fixed-point number to an integer.

Returns a tuple of the integer and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

The integer value can be of type [`i8`], [`i16`], [`i32`], [`i64`],
[`i128`], [`u8`], [`u16`], [`u32`], [`u64`], and [`u128`].

Any fractional bits are truncated.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_point_5 = Fix::from_int(5) / 2;
assert_eq!(two_point_5.overflowing_to_int::<i32>(), (2, false));
assert_eq!(",
                    if_signed_unsigned!(
                        $Signedness,
                        "(-two_point_5).overflowing_to_int::<i64>(), (-3",
                        "two_point_5.overflowing_to_int::<i64>(), (2",
                    ),
                    ", false));
let does_not_fit = fixed::",
                    stringify!($Fixed),
                    "::<fixed::frac::U0>::",
                    if_signed_unsigned!($Signedness, "from_bits(-1)", "max_value()"),
                    ";
let wrapped = ",
                    if_signed_unsigned!(
                        $Signedness,
                        concat!("1u", stringify!($nbits), ".wrapping_neg()"),
                        concat!("-1i", stringify!($nbits)),
                    ),
                    ";
assert_eq!(does_not_fit.overflowing_to_int::<",
                    if_signed_unsigned!($Signedness, "u", "i"),
                    stringify!($nbits),
                    ">(), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
",
                ),
                #[inline]
                pub fn overflowing_to_int<I>(self) -> (I, bool)
                where
                    I: Int,
                {
                    <I as SealedInt>::overflowing_from_fixed(self)
                }
            );

            doc_comment!(
                concat!(
                    "Creates a fixed-point number from a
floating-point number.

Returns a tuple of the fixed-point number and a [`bool`] indicating whether
an overflow has occurred. On overflow, the wrapped value is returned.

The floating-point value can be of type [`f32`] or [`f64`].
If the [`f16` feature] is enabled, it can also be of type [`f16`].

This method rounds to the nearest, with ties rounding to even.

# Panics

This method panics if the value is not [finite].

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 1.75 is 1.11 in binary
let from_bits = Fix::from_bits(0b111 << (4 - 2));
assert_eq!(Fix::overflowing_from_float(1.75f32), (from_bits, false));
assert_eq!(Fix::overflowing_from_float(",
                    if_signed_unsigned!($Signedness, "-1.75f64), (-", "1.75f64), ("),
                    "from_bits, false));
// 1.75 << (",
                    stringify!($nbits),
                    " - 4) wraps to binary 11000...
let large = 1.75 * 2f32.powi(",
                    stringify!($nbits),
                    " - 4);
let wrapped = Fix::from_bits(0b1100 << (",
                    stringify!($nbits),
                    " - 4));
assert_eq!(Fix::overflowing_from_float(large), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`f16` feature]: index.html#optional-features
[`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
",
                ),
                #[inline]
                pub fn overflowing_from_float<F>(val: F) -> ($Fixed<Frac>, bool)
                where
                    F: Float,
                {
                    if !val.is_finite() {
                        panic!("{} is not finite", val);
                    }
                    let (value, _, mut overflow) = val.to_fixed_dir_overflow(
                        Self::FRAC_NBITS,
                        Self::INT_NBITS,
                    );
                    let bits = if_signed_unsigned!(
                        $Signedness,
                        match value {
                            Widest::Unsigned(bits) => {
                                if (bits as <Self as SealedFixed>::Bits) < 0 {
                                    overflow = true;
                                }
                                bits as <Self as SealedFixed>::Bits
                            }
                            Widest::Negative(bits) => bits as <Self as SealedFixed>::Bits,
                        },
                        match value {
                            Widest::Unsigned(bits) => bits as <Self as SealedFixed>::Bits,
                            Widest::Negative(bits) => {
                                overflow = true;
                                bits as <Self as SealedFixed>::Bits
                            }
                        },
                    );
                    (SealedFixed::from_bits(bits), overflow)
                }
            );

            doc_comment!(
                concat!(
                    "
Returns the integer part.
",
                     if_signed_else_empty_str!(
                         $Signedness,
                         "
Note that since the numbers are stored in two’s
complement, negative numbers with non-zero fractional
parts will be rounded towards −∞, except in the case
where there are no integer bits, that is `",
                        stringify!($Fixed),
                        "<U",
                        stringify!($nbits),
                        ">`,
where the return value is always zero.
",
                    ),
                    "
# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 0010.0000
let two = Fix::from_int(2);
// 0010.0100
let two_and_quarter = two + two / 8;
assert_eq!(two_and_quarter.int(), two);",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
// 1101.0000
let three = Fix::from_int(3);
// 1101.1100
assert_eq!((-two_and_quarter).int(), -three);",
                    ),
                    "
```
",
                ),
                #[inline]
                pub fn int(self) -> $Fixed<Frac> {
                    let mask = Self::INT_MASK as <Self as SealedFixed>::Bits;
                    Self::from_bits(self.to_bits() & mask)
                }
            );

            doc_comment!(
                concat!(
                    "
Returns the fractional part.
",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
Note that since the numbers are stored in two’s
complement, the returned fraction will be non-negative
for negative numbers, except in the case where
there are no integer bits, that is `",
                        stringify!($Fixed),
                        "<U",
                        stringify!($nbits),
                        ">`
where the return value is always equal to `self`.
",
                    ),
                    "
# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
// 0000.0100
let quarter = Fix::from_int(1) / 4;
// 0010.0100
let two_and_quarter = quarter * 9;
assert_eq!(two_and_quarter.frac(), quarter);",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
// 0000.1100
let three_quarters = quarter * 3;
// 1101.1100
assert_eq!((-two_and_quarter).frac(), three_quarters);",
                    ),
                    "
```
",
                ),
                #[inline]
                pub fn frac(self) -> $Fixed<Frac> {
                    let mask = Self::FRAC_MASK as <Self as SealedFixed>::Bits;
                    Self::from_bits(self.to_bits() & mask)
                }
            );

            doc_comment!(
                concat!(
                    "
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
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.ceil(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).ceil(), Fix::from_int(-2));"
                    ),
                    "
```

[`wrapping_ceil`]: #method.wrapping_ceil
",
                ),
                #[inline]
                pub fn ceil(self) -> $Fixed<Frac> {
                    let (ceil, overflow) = self.overflowing_ceil();
                    debug_assert!(!overflow, "overflow");
                    let _ = overflow;
                    ceil
                }
            );

            doc_comment!(
                concat!(
                    "
Rounds to the next integer towards −∞.
",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
# Panics

If the result is too large to fit, the method panics in debug mode. In
release mode, the method may either panic or wrap the value, with the
current implementation wrapping the value. It is not considered a
breaking change if in the future the method panics even in release
mode; if wrapping is the required behavior use [`wrapping_floor`]
instead.

Overflow can only occur when there are zero integer bits.
",
                    ),
                    "
# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.floor(), Fix::from_int(2));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).floor(), Fix::from_int(-3));",
                    ),
                    "
```

[`wrapping_floor`]: #method.wrapping_floor
",
                ),
                #[inline]
                pub fn floor(self) -> $Fixed<Frac> {
                    let (floor, overflow) = self.overflowing_floor();
                    debug_assert!(!overflow, "overflow");
                    let _ = overflow;
                    floor
                }
            );

            doc_comment!(
                concat!(
                    "
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
type Fix = fixed::",
                    stringify!($Fixed),
                    r"<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.round(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).round(), Fix::from_int(-3));",
                    ),
                    "
```

[`wrapping_round`]: #method.wrapping_round
",
                ),
                #[inline]
                pub fn round(self) -> $Fixed<Frac> {
                    let (round, overflow) = self.overflowing_round();
                    debug_assert!(!overflow, "overflow");
                    let _ = overflow;
                    round
                }
            );

            doc_comment!(
                concat!(
                    "
Checked ceil. Rounds to the next integer towards +∞, returning
[`None`] on overflow.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_ceil(), Some(Fix::from_int(3)));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).checked_ceil(), Some(Fix::from_int(-2)));",
                    ),
                    "
assert!(Fix::max_value().checked_ceil().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
",
                ),
                #[inline]
                pub fn checked_ceil(self) -> Option<$Fixed<Frac>> {
                    let (ceil, overflow) = self.overflowing_ceil();
                    if overflow { None } else { Some(ceil) }
                }
            );

            doc_comment!(
                concat!(
                    "
Checked floor. Rounds to the next integer towards −∞.",
                    if_signed_unsigned!(
                        $Signedness,
                        "
Returns [`None`] on overflow.

Overflow can only occur when there are zero integer bits.",
                        "
Checked floor. Rounds to the next integer towards −∞.
Always returns [`Some`] for unsigned values.",
                    ),
                    "

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_floor(), Some(Fix::from_int(2)));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).checked_floor(), Some(Fix::from_int(-3)));
type AllFrac = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::",
                        stringify!($Len),
                        ">;
assert!(AllFrac::min_value().checked_floor().is_none());"
                    ),
                    "
```
",
                    if_signed_unsigned!(
                        $Signedness,
                        "
[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None",
                        "
[`Some`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.Some",
                    ),
                    "
",
                ),
                #[inline]
                pub fn checked_floor(self) -> Option<$Fixed<Frac>> {
                    let (floor, overflow) = self.overflowing_floor();
                    if overflow { None } else { Some(floor) }
                }
            );

            doc_comment!(
                concat!(
                    "
Checked round. Rounds to the nearest integer, with ties rounded away
from zero, returning [`None`] on overflow.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.checked_round(), Some(Fix::from_int(3)));",
                        if_signed_else_empty_str!(
                            $Signedness,
                            "
assert_eq!((-two_half).checked_round(), Some(Fix::from_int(-3)));",
                        ),
                        "
assert!(Fix::max_value().checked_round().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
",
                ),
                #[inline]
                pub fn checked_round(self) -> Option<$Fixed<Frac>> {
                    let (round, overflow) = self.overflowing_round();
                    if overflow { None } else { Some(round) }
                }
            );

            doc_comment!(
                concat!(
                    "
Saturating ceil. Rounds to the next integer towards +∞, saturating on
overflow.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_ceil(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).saturating_ceil(), Fix::from_int(-2));",
                    ),
                    "
assert_eq!(Fix::max_value().saturating_ceil(), Fix::max_value());
```
",
                ),
                #[inline]
                pub fn saturating_ceil(self) -> $Fixed<Frac> {
                    let (ceil, overflow) = self.overflowing_ceil();
                    if overflow { Self::max_value() } else { ceil }
                }
            );

            doc_comment!(
                concat!(
                    if_signed_unsigned!(
                        $Signedness,
                        "
Saturating floor. Rounds to the next integer towards −∞, saturating on
overflow.

Overflow can only occur when there are zero integer bits.",
                        "
Saturating floor. Rounds to the next integer towards −∞. Cannot
overflow for unsigned values.",
                    ),
                    "

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_floor(), Fix::from_int(2));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).saturating_floor(), Fix::from_int(-3));
type AllFrac = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::",
                        stringify!($Len),
                        ">;
assert_eq!(AllFrac::min_value().saturating_floor(), AllFrac::min_value());",
                    ),
                    "
```
",
                ),
                #[inline]
                pub fn saturating_floor(self) -> $Fixed<Frac> {
                    let (floor, overflow) = self.overflowing_floor();
                    if overflow { Self::min_value() } else { floor }
                }
            );

            doc_comment!(
                concat!(
                    "
Saturating round. Rounds to the nearest integer, with ties rounded
away from zero, and saturating on overflow.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.saturating_round(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).saturating_round(), Fix::from_int(-3));",
                    ),
                    "
assert_eq!(Fix::max_value().saturating_round(), Fix::max_value());
```
",
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
            );

            doc_comment!(
                concat!(
                    "
Wrapping ceil. Rounds to the next integer towards +∞, wrapping on overflow.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_ceil(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).wrapping_ceil(), Fix::from_int(-2));",
                    ),
                    "
assert_eq!(Fix::max_value().wrapping_ceil(), Fix::min_value());
```
",
                ),
                #[inline]
                pub fn wrapping_ceil(self) -> $Fixed<Frac> {
                    self.overflowing_ceil().0
                }
            );

            doc_comment!(
                concat!(
                    if_signed_unsigned!(
                        $Signedness,
                        "
Wrapping floor. Rounds to the next integer towards −∞, wrapping on overflow.

Overflow can only occur when there are zero integer bits.",
                        "
Wrapping floor. Rounds to the next integer towards −∞.
Cannot overflow for unsigned values.",
                    ),
                    "

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_floor(), Fix::from_int(2));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).wrapping_floor(), Fix::from_int(-3));
type AllFrac = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::",
                        stringify!($Len),
                        ">;
assert_eq!(AllFrac::min_value().wrapping_floor(), AllFrac::from_int(0));",
                    ),
                    "
```
",
                ),
                #[inline]
                pub fn wrapping_floor(self) -> $Fixed<Frac> {
                    self.overflowing_floor().0
                }
            );

            doc_comment!(
                concat!(
                    "
Wrapping round. Rounds to the next integer to the nearest, with ties
rounded away from zero, and wrapping on overflow.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.wrapping_round(), Fix::from_int(3));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).wrapping_round(), Fix::from_int(-3));",
                    ),
                    "
assert_eq!(Fix::max_value().wrapping_round(), Fix::min_value());
```
",
                ),
                #[inline]
                pub fn wrapping_round(self) -> $Fixed<Frac> {
                    self.overflowing_round().0
                }
            );

            doc_comment!(
                concat!(
                    "
Overflowing ceil. Rounds to the next integer towards +∞.

Returns a tuple of the fixed-point number and a [`bool`], indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_ceil(), (Fix::from_int(3), false));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).overflowing_ceil(), (Fix::from_int(-2), false));"
                    ),
                    "
assert_eq!(Fix::max_value().overflowing_ceil(), (Fix::min_value(), true));
```
",
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
                    let int_lsb = Self::INT_LSB as <Self as SealedFixed>::Bits;
                    let increment = Self::from_bits(int_lsb);
                        if_signed! {
                            $Signedness;
                            if Self::int_bits() == 1 {
                                return int.overflowing_sub(increment);
                            }
                        }
                        int.overflowing_add(increment)
                    }
            );

            doc_comment!(
                concat!(
                    "
Overflowing floor. Rounds to the next integer towards −∞.
",
                    if_signed_unsigned!(
                        $Signedness,
                        "
Returns a tuple of the fixed-point number and a [`bool`], indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned. Overflow can only occur when there are zero integer bits.",
                        "
Returns a tuple of the fixed-point number and [`false`][`bool`].",
                    ),
                    "

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_floor(), (Fix::from_int(2), false));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).overflowing_floor(), (Fix::from_int(-3), false));
type AllFrac = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::",
                        stringify!($Len),
                        ">;
assert_eq!(AllFrac::min_value().overflowing_floor(), (AllFrac::from_int(0), true));",
                    ),
                    "
```
",
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
            );

            doc_comment!(
                concat!(
                    "
Overflowing round. Rounds to the next integer to the nearest,
with ties rounded away from zero.

Returns a tuple of the fixed-point number and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let two_half = Fix::from_int(5) / 2;
assert_eq!(two_half.overflowing_round(), (Fix::from_int(3), false));",
                    if_signed_else_empty_str!(
                        $Signedness,
                        "
assert_eq!((-two_half).overflowing_round(), (Fix::from_int(-3), false));",
                    ),
                    "
assert_eq!(Fix::max_value().overflowing_round(), (Fix::min_value(), true));
```
",
                ),
                #[inline]
                pub fn overflowing_round(self) -> ($Fixed<Frac>, bool) {
                    let int = self.int();
                    let frac_msb = Self::FRAC_MSB as <Self as SealedFixed>::Bits;
                    if (self.to_bits() & frac_msb) == 0 {
                        return (int, false);
                    }
                    let int_lsb = Self::INT_LSB as <Self as SealedFixed>::Bits;
                    let increment = Self::from_bits(int_lsb);
                    if_signed! {
                        $Signedness;
                        let tie = self.frac().to_bits() == frac_msb;
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
            );

            pass_method! {
                concat!(
                    "
Returns the number of ones in the binary representation.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let f = Fix::from_bits(0b11_0010);
assert_eq!(f.count_ones(), 3);
```
",
                ),
                $Fixed($Inner) => fn count_ones(self) -> u32
            }
            pass_method! {
                concat!(
                    "
Returns the number of zeros in the binary representation.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let f = Fix::from_bits(!0b11_0010);
assert_eq!(f.count_zeros(), 3);
```
",
                ),
                $Fixed($Inner) => fn count_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "
Returns the number of leading zeros in the binary representation.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.leading_zeros(), ", stringify!($nbits), " - 6);
```
",
                ),
                $Fixed($Inner) => fn leading_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "
Returns the number of trailing zeros in the binary representation.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.trailing_zeros(), 5);
```
",
                ),
                $Fixed($Inner) => fn trailing_zeros(self) -> u32
            }
            pass_method! {
                concat!(
                    "
Shifts to the left by *n* bits, wrapping the truncated bits to the right end.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let bits: ",
                    stringify!($Inner),
                    " = (0b111 << (",
                    stringify!($nbits),
                    " - 3)) | 0b1010;
let rot = 0b1010111;
assert_eq!(bits.rotate_left(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_left(3), Fix::from_bits(rot));
```
",
                ),
                $Fixed($Inner) => fn rotate_left(self, n: u32)
            }
            pass_method! {
                concat!(
                    "
Shifts to the right by *n* bits, wrapping the truncated bits to the left end.

# Examples

```rust
type Fix = fixed::",
                    stringify!($Fixed),
                    "<fixed::frac::U4>;
let bits: ",
                    stringify!($Inner),
                    " = 0b1010111;
let rot = (0b111 << (",
                    stringify!($nbits),
                    " - 3)) | 0b1010;
assert_eq!(bits.rotate_right(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_right(3), Fix::from_bits(rot));
```
",
                ),
                $Fixed($Inner) => fn rotate_right(self, n: u32)
            }

            /// Checked negation.
            #[inline]
            pub fn checked_neg(self) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_neg(self.to_bits()).map(Self::from_bits)
            }

            /// Checked fixed-point addition.
            #[inline]
            pub fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_add(self.to_bits(), rhs.to_bits()).map(Self::from_bits)
            }

            /// Checked fixed-point subtraction.
            #[inline]
            pub fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_sub(self.to_bits(), rhs.to_bits()).map(Self::from_bits)
            }

            /// Checked fixed-point multiplication.
            #[inline]
            pub fn checked_mul(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                match dir {
                    Ordering::Equal => Some(Self::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point division.
            #[inline]
            pub fn checked_div(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                if rhs.to_bits() == 0 {
                    return None;
                }
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                match dir {
                    Ordering::Equal => Some(Self::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point multiplication by integer.
            #[inline]
            pub fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_mul(self.to_bits(), rhs).map(Self::from_bits)
            }

            /// Checked fixed-point division by integer.
            #[inline]
            pub fn checked_div_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_div(self.to_bits(), rhs).map(Self::from_bits)
            }

            /// Checked fixed-point remainder for division by integer.
            #[inline]
            pub fn checked_rem_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_rem(self.to_bits(), rhs).map(Self::from_bits)
            }

            /// Checked fixed-point left shift.
            #[inline]
            pub fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shl(self.to_bits(), rhs).map(Self::from_bits)
            }

            /// Checked fixed-point right shift.
            #[inline]
            pub fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shr(self.to_bits(), rhs).map(Self::from_bits)
            }

            if_signed! {
                $Signedness;
                /// Checked absolute value.
                #[inline]
                pub fn checked_abs(self) -> Option<$Fixed<Frac>> {
                    <$Inner>::checked_abs(self.to_bits()).map(Self::from_bits)
                }
            }

            /// Saturating fixed-point addition.
            #[inline]
            pub fn saturating_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::saturating_add(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point subtraction.
            #[inline]
            pub fn saturating_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::saturating_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point multiplication.
            #[inline]
            pub fn saturating_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                match dir {
                    Ordering::Equal => Self::from_bits(ans),
                    Ordering::Less => Self::max_value(),
                    Ordering::Greater => Self::min_value(),
                }
            }

            /// Saturating fixed-point division.
            #[inline]
            pub fn saturating_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                match dir {
                    Ordering::Equal => Self::from_bits(ans),
                    Ordering::Less => Self::max_value(),
                    Ordering::Greater => Self::min_value(),
                }
            }

            /// Saturating fixed-point multiplication by integer.
            #[inline]
            pub fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::saturating_mul(self.to_bits(), rhs))
            }

            /// Wrapping negation.
            #[inline]
            pub fn wrapping_neg(self) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_neg(self.to_bits()))
            }

            /// Wrapping fixed-point addition.
            #[inline]
            pub fn wrapping_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_add(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point subtraction.
            #[inline]
            pub fn wrapping_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point multiplication.
            #[inline]
            pub fn wrapping_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                Self::from_bits(ans)
            }

            /// Wrapping fixed-point division.
            #[inline]
            pub fn wrapping_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                Self::from_bits(ans)
            }

            /// Wrapping fixed-point multiplication by integer.
            #[inline]
            pub fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_mul(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point division by integer.
            #[inline]
            pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_div(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point remainder for division by integer.
            #[inline]
            pub fn wrapping_rem_int(self, rhs: $Inner) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_rem(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point left shift.
            #[inline]
            pub fn wrapping_shl(self, rhs: u32) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_shl(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point right shift.
            #[inline]
            pub fn wrapping_shr(self, rhs: u32) -> $Fixed<Frac> {
                Self::from_bits(<$Inner>::wrapping_shr(self.to_bits(), rhs))
            }

            if_signed! {
                $Signedness;
                /// Wrapping absolute value.
                #[inline]
                pub fn wrapping_abs(self) -> $Fixed<Frac> {
                    Self::from_bits(<$Inner>::wrapping_abs(self.to_bits()))
                }
            }

            /// Overflowing negation.
            #[inline]
            pub fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_neg(self.to_bits());
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point addition.
            #[inline]
            pub fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_add(self.to_bits(), rhs.to_bits());
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point subtraction.
            #[inline]
            pub fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_sub(self.to_bits(), rhs.to_bits());
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point multiplication.
            #[inline]
            pub fn overflowing_mul(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::U32);
                (Self::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point division.
            #[inline]
            pub fn overflowing_div(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::U32);
                (Self::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point multiplication by integer.
            #[inline]
            pub fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_mul(self.to_bits(), rhs);
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point division by integer.
            #[inline]
            pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_div(self.to_bits(), rhs);
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point remainder for division by integer.
            #[inline]
            pub fn overflowing_rem_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_rem(self.to_bits(), rhs);
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point left shift.
            #[inline]
            pub fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shl(self.to_bits(), rhs);
                (Self::from_bits(ans), o)
            }

            /// Overflowing fixed-point right shift.
            #[inline]
            pub fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shr(self.to_bits(), rhs);
                (Self::from_bits(ans), o)
            }

            if_signed! {
                $Signedness;
                /// Overflowing absolute value.
                #[inline]
                pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = <$Inner>::overflowing_abs(self.to_bits());
                    (Self::from_bits(ans), o)
                }
            }

            if_unsigned! {
                $Signedness;
                pass_method! {
                    concat!(
                        "
Returns `true` if the fixed-point number is
2<sup><i>k</i></sup> for some <i>k</i>.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert!(!three_eights.is_power_of_two());
assert!(half.is_power_of_two());
```
",
                    ),
                    $Fixed($Inner) => fn is_power_of_two(self) -> bool
                }
            }

            if_unsigned! {
                $Signedness;
                pass_method! {
                    concat!(
                        "
Returns the smallest power of two ≥ `self`.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.next_power_of_two(), half);
assert_eq!(half.next_power_of_two(), half);
```
",
                    ),
                    $Fixed($Inner) => fn next_power_of_two(self)
                }
            }

            if_unsigned! {
                $Signedness;
                doc_comment!(
                    concat!(
                        "
Returns the smallest power of two ≥ `self`, or [`None`]
if the next power of two is too large to represent.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.checked_next_power_of_two(), Some(half));
assert!(Fix::max_value().checked_next_power_of_two().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
",
                    ),
                    #[inline]
                    pub fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                        <$Inner>::checked_next_power_of_two(self.to_bits()).map(Self::from_bits)
                    }
                );
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "
Returns the absolute value.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
let five = Fix::from_int(5);
let minus_five = Fix::from_int(-5);
assert_eq!(five.abs(), five);
assert_eq!(minus_five.abs(), five);
```
",
                    ),
                    $Fixed($Inner) => fn abs(self)
                }
            }

            if_signed! {
                $Signedness;
                doc_comment!(
                    concat!(
                        "
Returns a number representing the sign of `self`.

# Panics

This method panics:
  * if the value is positive and the fixed-point number has zero
    or one integer bits such that it cannot hold the value 1.
  * if the value is negative and the fixed-point number has zero
    integer bits, such that it cannot hold the value −1.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
assert_eq!(Fix::from_int(5).signum(), 1);
assert_eq!(Fix::from_int(0).signum(), 0);
assert_eq!(Fix::from_int(-5).signum(), -1);
```
",
                    ),
                    #[inline]
                    pub fn signum(self) -> $Fixed<Frac> {
                        match self.to_bits().cmp(&0) {
                            Ordering::Equal => Self::from_bits(0),
                            Ordering::Greater => Self::one().expect("overflow"),
                            Ordering::Less => Self::minus_one().expect("overflow"),
                        }
                    }
                );
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "
Returns `true` if the number is > 0.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
assert!(Fix::from_int(5).is_positive());
assert!(!Fix::from_int(0).is_positive());
assert!(!Fix::from_int(-5).is_positive());
```
",
                    ),
                    $Fixed($Inner) => fn is_positive(self) -> bool
                }
            }

            if_signed! {
                $Signedness;
                pass_method! {
                    concat!(
                        "
Returns `true` if the number is < 0.

# Examples

```rust
type Fix = fixed::",
                        stringify!($Fixed),
                        "<fixed::frac::U4>;
assert!(!Fix::from_int(5).is_negative());
assert!(!Fix::from_int(0).is_negative());
assert!(Fix::from_int(-5).is_negative());
```
",
                    ),
                    $Fixed($Inner) => fn is_negative(self) -> bool
                }
            }

            doc_comment!(
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "`, rounding towards +∞.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.ceil().to_int::<_>() instead")]
                #[inline]
                pub fn to_int_ceil(self) -> $Inner {
                    if let Some(ceil) = self.checked_ceil() {
                        ceil.to_int()
                    } else {
                        self.floor().to_int::<$Inner>() + 1
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "` rounding towards −∞.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.floor().to_int::<_>() instead")]
                #[inline]
                pub fn to_int_floor(self) -> $Inner {
                    if let Some(floor) = self.checked_floor() {
                        floor.to_int()
                    } else {
                        self.ceil().to_int::<$Inner>() - 1
                    }
                }
            );

            doc_comment!(
                concat!(
                    "Converts the fixed-point number of type `",
                    stringify!($Fixed),
                    "` to an integer of type `",
                    stringify!($Inner),
                    "` rounding towards the nearest. Ties are rounded away from zero.\n",
                ),
                #[deprecated(since = "0.2.0", note = "use f.round().to_int::<_>() instead")]
                #[inline]
                pub fn to_int_round(self) -> $Inner {
                    if let Some(round) = self.checked_round() {
                        round.to_int()
                    } else if let Some(floor) = self.checked_floor() {
                        floor.to_int::<$Inner>() + 1
                    } else {
                        self.ceil().to_int::<$Inner>() - 1
                    }
                }
            );


            #[cfg(feature = "f16")]
            deprecated_from_float! { fn from_f16(f16) -> $Fixed<Frac> }
            deprecated_from_float! { fn from_f32(f32) -> $Fixed<Frac> }
            deprecated_from_float! { fn from_f64(f64) -> $Fixed<Frac> }

            #[cfg(feature = "f16")]
            deprecated_to_float! { fn to_f16($Fixed) -> f16 }
            deprecated_to_float! { fn to_f32($Fixed) -> f32 }
            deprecated_to_float! { fn to_f64($Fixed) -> f64 }
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
    #[test]
    fn rounding() {
        use frac::{U16, U32};

        type I0F32 = FixedI32<U32>;

        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_int::<i32>(), -1);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), true));

        // -0.5 + Δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_int::<i32>(), -1);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), false));

        // 0.5 - Δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (I0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (I0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I0F32::from_int(0), false));

        type U0F32 = FixedU32<U32>;

        // 0.5 - Δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), false));

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), true));

        // 0.5 + Δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U0F32::from_int(0), true));
        assert_eq!(f.overflowing_floor(), (U0F32::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U0F32::from_int(0), true));

        type I16F16 = FixedI32<U16>;

        // -3.5 - Δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_int::<i32>(), -4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-4), false));

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_int::<i32>(), -4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-4), false));

        // -3.5 + Δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_int::<i32>(), -4);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(-3), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-4), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-3), false));

        // -0.5 - Δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_int::<i32>(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-1), false));

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_int::<i32>(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(-1), false));

        // -0.5 + Δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_int::<i32>(), -1);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(-1), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(0), false));

        // 0.5 - Δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(0), false));

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(1), false));

        // 0.5 + Δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(1), false));

        // 3.5 - Δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(3), false));

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(4), false));

        // 3.5 + Δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (I16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (I16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (I16F16::from_int(4), false));

        type U16F16 = FixedU32<U16>;

        // 0.5 - Δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(0), false));

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(1), false));

        // 0.5 + Δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int::<i32>(), 0);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(1), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(0), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(1), false));

        // 3.5 - Δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(3), false));

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(4), false));

        // 3.5 + Δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int::<i32>(), 3);
        assert_eq!(f.overflowing_ceil(), (U16F16::from_int(4), false));
        assert_eq!(f.overflowing_floor(), (U16F16::from_int(3), false));
        assert_eq!(f.overflowing_round(), (U16F16::from_int(4), false));
    }
}
