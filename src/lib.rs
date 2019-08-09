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

Various conversion methods are available:

  * All lossless infallible conversions between fixed-point numbers
    and numeric primitives are implemented. That is, you can use
    [`From`] or [`Into`] for the conversions that always work without
    losing any bits.
  * For infallible conversions that are not lossless because the
    source type may have more fractional bits than the destination
    type, [`LossyFrom`] and [`LossyInto`] can be used; these will
    truncate any excess fractional bits in the source value.
  * Checked conversions are provided between all types using the
    [`FromFixed`] and [`ToFixed`] traits, or using the inherent methods
    in the fixed-point types themselves.

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
// we can also compare directly to integers
assert_eq!(six_and_third.ceil(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
<code>[FixedI32][`FixedI32`]&lt;[frac::U12][`frac::U12`]&gt;</code>.
The unsigned counterpart would be [`U20F12`]. Aliases are provided for
all combinations of integer and fractional bits adding up to a total
of eight, 16, 32, 64 or 128 bits.

```rust
// −8 ≤ I4F4 < 8 with steps of 1/16 (about 0.06)
use fixed::types::I4F4;
let a = I4F4::from_int(1);
// multiplication and division by integers are possible
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
fixed = "0.4.0"
```

If you are using the 2015 Rust edition, you also need to declare it by
adding this to your crate root (usually *lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

The *fixed* crate requires rustc version 1.31.0 or later.

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
version = "0.4.0"
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
[`FromFixed`]: traits/trait.FromFixed.html
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`I20F12`]: types/type.I20F12.html
[`I4F12`]: types/type.I4F12.html
[`I4F4`]: types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/std/convert/trait.Into.html
[`LossyFrom`]: traits/trait.LossyFrom.html
[`LossyInto`]: traits/trait.LossyInto.html
[`ToFixed`]: traits/trait.ToFixed.html
[`U20F12`]: types/type.U20F12.html
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`frac::U12`]: frac/type.U12.html
[`from_fixed`]: struct.FixedI8.html#method.from_fixed
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.4.0")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

#[macro_use]
mod macros;

mod arith;
mod cmp;
pub mod consts;
mod convert;
mod display;
pub mod frac;
mod from_str;
pub mod sealed;
mod sealed_fixed;
mod sealed_float;
mod sealed_int;
#[cfg(feature = "serde")]
mod serdeize;
pub mod traits;
pub mod types;
mod wide_div;
mod wrapping;

pub use crate::wrapping::Wrapping;
use crate::{
    arith::MulDivDir,
    frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8},
    sealed::{Fixed, Float, Int, SealedFixed, SealedFloat, SealedInt},
};
use core::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

/// A prelude for users of the *fixed* crate.
///
/// This prelude is similar to the [standard library’s
/// prelude][prelude] in that you’ll almost always want to import its
/// entire contents, but unlike the standard library’s prelude you’ll
/// have to do so manually:
///
/// ```
/// # #[allow(unused_imports)]
/// use fixed::prelude::*;
/// ```
///
/// The prelude may grow over time as additional items see ubiquitous use.
///
/// [prelude]: https://doc.rust-lang.org/nightly/std/prelude/index.html
pub mod prelude {
    pub use crate::traits::{FromFixed, ToFixed};
}

#[macro_use]
mod macros_from_to;
#[macro_use]
mod macros_round;
#[macro_use]
mod macros_checked_arith;

macro_rules! fixed {
    ($description:expr, $Fixed:ident($Inner:ty, $Len:tt, $s_nbits:expr), $Signedness:tt) => {
        fixed! {
            $description,
            $Fixed[stringify!($Fixed)]($Inner[stringify!($Inner)], $Len, $s_nbits),
            $Signedness
        }
    };
    (
        $description:expr,
        $Fixed:ident[$s_fixed:expr]($Inner:ty[$s_inner:expr], $Len:tt, $s_nbits:expr),
        $Signedness:tt
    ) => {
        comment!(
            $description,
            " with `Frac` fractional bits.

Currently `Frac` is an [`Unsigned`] as provided by the
[typenum crate]; it is planned to move to [const generics] when they
are implemented by the Rust compiler.

# Examples

```rust
use fixed::frac::U3;
use fixed::",
            $s_fixed,
            ";
let eleven = ",
            $s_fixed,
            "::<U3>::from_int(11);
assert_eq!(eleven, ",
            $s_fixed,
            "::<U3>::from_bits(11 << 3));
assert_eq!(eleven, 11);
assert_eq!(eleven.to_string(), \"11.0\");
let two_point_75 = eleven / 4;
assert_eq!(two_point_75, ",
            $s_fixed,
            "::<U3>::from_bits(11 << 1));
assert_eq!(two_point_75, 2.75);
assert_eq!(two_point_75.to_string(), \"2.8\");
```

[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
[typenum crate]: https://crates.io/crates/typenum
";
            #[repr(transparent)]
            pub struct $Fixed<Frac>
            where
                Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
            {
                bits: $Inner,
                phantom: PhantomData<Frac>,
            }
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
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.to_bits().hash(state);
            }
        }

        impl<Frac> $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$Len, Output = True>,
        {
            delegate!(
                "Returns the smallest value that can be represented.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
assert_eq!(Fix::min_value(), Fix::from_bits(",
                $s_inner,
                "::min_value()));
```
";
                $Fixed($Inner) => fn min_value()
            );
            delegate!(
                "Returns the largest value that can be represented.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
assert_eq!(Fix::max_value(), Fix::from_bits(",
                $s_inner,
                "::max_value()));
```
";
                $Fixed($Inner) => fn max_value()
            );

            comment!(
                "Returns the number of integer bits.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U6>;
assert_eq!(Fix::int_nbits(), ",
                $s_nbits,
                " - 6);
```
";
                #[inline]
                pub fn int_nbits() -> u32 {
                    Self::INT_NBITS
                }
            );

            comment!(
                    "Returns the number of fractional bits.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U6>;
assert_eq!(Fix::frac_nbits(), 6);
```
";
                #[inline]
                pub fn frac_nbits() -> u32 {
                    Self::FRAC_NBITS
                }
            );

            fixed_from_to! { $Fixed[$s_fixed]($Inner[$s_inner], $s_nbits), $Signedness }
            fixed_round! { $Fixed[$s_fixed]($s_nbits), $Signedness }

            delegate!(
                "Returns the number of ones in the binary
representation.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let f = Fix::from_bits(0b11_0010);
assert_eq!(f.count_ones(), 3);
```
";
                $Fixed($Inner) => fn count_ones(self) -> u32
            );
            delegate!(
                "Returns the number of zeros in the binary
representation.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let f = Fix::from_bits(!0b11_0010);
assert_eq!(f.count_zeros(), 3);
```
";
                $Fixed($Inner) => fn count_zeros(self) -> u32
            );
            delegate!(
                "Returns the number of leading zeros in the binary
representation.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.leading_zeros(), ",
                $s_nbits,
                " - 6);
```
";
                $Fixed($Inner) => fn leading_zeros(self) -> u32
            );
            delegate!(
                "Returns the number of trailing zeros in the binary
representation.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.trailing_zeros(), 5);
```
";
                $Fixed($Inner) => fn trailing_zeros(self) -> u32
            );
            delegate!(
                "Shifts to the left by *n* bits, wrapping the
truncated bits to the right end.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let bits: ",
                $s_inner,
                " = (0b111 << (",
                $s_nbits,
                " - 3)) | 0b1010;
let rot = 0b1010111;
assert_eq!(bits.rotate_left(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_left(3), Fix::from_bits(rot));
```
";
                $Fixed($Inner) => fn rotate_left(self, n: u32)
            );
            delegate!(
                "Shifts to the right by *n* bits, wrapping the
truncated bits to the left end.

# Examples

```rust
type Fix = fixed::",
                $s_fixed,
                "<fixed::frac::U4>;
let bits: ",
                $s_inner,
                " = 0b1010111;
let rot = (0b111 << (",
                $s_nbits,
                " - 3)) | 0b1010;
assert_eq!(bits.rotate_right(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_right(3), Fix::from_bits(rot));
```
";
                $Fixed($Inner) => fn rotate_right(self, n: u32)
            );

            if_signed! {
                $Signedness;
                delegate!(
                    "Returns the absolute value.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
let five = Fix::from_int(5);
let minus_five = Fix::from_int(-5);
assert_eq!(five.abs(), five);
assert_eq!(minus_five.abs(), five);
```
";
                    $Fixed($Inner) => fn abs(self)
                );

                comment!(
                    "Returns a number representing the sign of `self`.

# Panics

When debug assertions are enabled, this method panics
  * if the value is positive and the fixed-point number has zero
    or one integer bits such that it cannot hold the value 1.
  * if the value is negative and the fixed-point number has zero
    integer bits, such that it cannot hold the value −1.

When debug assertions are not enabled, the wrapped value can be
returned in those cases, but it is not considered a breaking change if
in the future it panics; using this method when 1 and −1 cannot be
represented is almost certainly a bug.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
assert_eq!(Fix::from_int(5).signum(), 1);
assert_eq!(Fix::from_int(0).signum(), 0);
assert_eq!(Fix::from_int(-5).signum(), -1);
```
";
                    #[inline]
                    pub fn signum(self) -> $Fixed<Frac> {
                        match self.to_bits().cmp(&0) {
                            Ordering::Equal => Self::from_bits(0),
                            Ordering::Greater => 1.to_fixed(),
                            Ordering::Less => (-1).to_fixed(),
                        }
                    }
                );
            }

            fixed_checked_arith! { $Fixed[$s_fixed]($Inner, $s_nbits), $Signedness }

            if_unsigned! {
                $Signedness;
                delegate!(
                    "Returns [`true`][`bool`] if the fixed-point number is
2<sup><i>k</i></sup> for some integer <i>k</i>.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert!(!three_eights.is_power_of_two());
assert!(half.is_power_of_two());
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    $Fixed($Inner) => fn is_power_of_two(self) -> bool
                );

                delegate!(
                    "Returns the smallest power of two ≥ `self`.

# Panics

When debug assertions are enabled, panics if the next power of two is
too large to represent. When debug assertions are not enabled, zero
can be returned, but it is not considered a breaking change if in the
future it panics.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.next_power_of_two(), half);
assert_eq!(half.next_power_of_two(), half);
```
";
                    $Fixed($Inner) => fn next_power_of_two(self)
                );

                comment!(
                    "Returns the smallest power of two ≥ `self`, or
[`None`] if the next power of two is too large to represent.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.checked_next_power_of_two(), Some(half));
assert!(Fix::max_value().checked_next_power_of_two().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
";
                    #[inline]
                    pub fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                        <$Inner>::checked_next_power_of_two(self.to_bits()).map(Self::from_bits)
                    }
                );
            }

            if_signed! {
                $Signedness;
                delegate!(
                    "Returns [`true`][`bool`] if the number is > 0.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
assert!(Fix::from_int(5).is_positive());
assert!(!Fix::from_int(0).is_positive());
assert!(!Fix::from_int(-5).is_positive());
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    $Fixed($Inner) => fn is_positive(self) -> bool
                );

                delegate!(
                    "Returns [`true`][`bool`] if the number is < 0.

# Examples

```rust
type Fix = fixed::",
                    $s_fixed,
                    "<fixed::frac::U4>;
assert!(!Fix::from_int(5).is_negative());
assert!(!Fix::from_int(0).is_negative());
assert!(Fix::from_int(-5).is_negative());
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    $Fixed($Inner) => fn is_negative(self) -> bool
                );
            }
        }
    };
}

fixed! { "An eight-bit fixed-point unsigned integer", FixedU8(u8, U8, "8"), Unsigned }
fixed! { "A 16-bit fixed-point unsigned integer", FixedU16(u16, U16, "16"), Unsigned }
fixed! { "A 32-bit fixed-point unsigned integer", FixedU32(u32, U32, "32"), Unsigned }
fixed! { "A 64-bit fixed-point unsigned integer", FixedU64(u64, U64, "64"), Unsigned }
fixed! { "A 128-bit fixed-point unsigned integer", FixedU128(u128, U128, "128"), Unsigned }
fixed! { "An eight-bit fixed-point signed integer", FixedI8(i8, U8, "8"), Signed }
fixed! { "A 16-bit fixed-point signed integer", FixedI16(i16, U16, "16"), Signed }
fixed! { "A 32-bit fixed-point signed integer", FixedI32(i32, U32, "32"), Signed }
fixed! { "A 64-bit fixed-point signed integer", FixedI64(i64, U64, "64"), Signed }
fixed! { "A 128-bit fixed-point signed integer", FixedI128(i128, U128, "128"), Signed }

#[cfg(test)]
mod tests {
    use crate::*;

    #[cfg_attr(feature = "cargo-clippy", allow(clippy::cognitive_complexity))]
    #[test]
    fn rounding() {
        use crate::frac::{U16, U32};

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
