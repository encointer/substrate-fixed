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

macro_rules! deprecated_from_float {
    (fn $method:ident($Float:ident) -> $Fixed:ident<$Frac:ident>) => {
        comment!(
            "Creates a fixed-point number from `",
            stringify!($Float),
            "`.

This method has been replaced by [`checked_from_float`].

[`checked_from_float`]: #method.checked_from_float
";
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
        comment!(
            "Converts the fixed-point number to `",
            stringify!($Float),
            "`.

This method has been replaced by [`to_float`].

[`to_float`]: #method.to_float
";
            #[deprecated(since = "0.2.0", note = "replaced by to_float")]
            #[inline]
            pub fn $method(self) -> $Float {
                self.to_float()
            }
        );
    };
}

macro_rules! fixed_deprecated {
    ($Fixed:ident($Inner:ty)) => {
        /// Returns the number of integer bits.
        #[inline]
        #[deprecated(since = "0.3.0", note = "renamed to int_nbits")]
        pub fn int_bits() -> u32 {
            Self::int_nbits()
        }

        /// Returns the number of fractional bits.
        #[inline]
        #[deprecated(since = "0.3.0", note = "renamed to frac_nbits")]
        pub fn frac_bits() -> u32 {
            Self::frac_nbits()
        }

        /// Converts the fixed-point number to an integer,
        /// rounding towards +∞.
        #[deprecated(since = "0.2.0", note = "use f.ceil().to_int::<_>() instead")]
        #[inline]
        pub fn to_int_ceil(self) -> $Inner {
            if let Some(ceil) = self.checked_ceil() {
                ceil.to_int()
            } else {
                self.floor().to_int::<$Inner>() + 1
            }
        }

        /// Converts the fixed-point number to an integer, rounding
        /// towards −∞.
        #[deprecated(since = "0.2.0", note = "use f.floor().to_int::<_>() instead")]
        #[inline]
        pub fn to_int_floor(self) -> $Inner {
            if let Some(floor) = self.checked_floor() {
                floor.to_int()
            } else {
                self.ceil().to_int::<$Inner>() - 1
            }
        }

        /// Converts the fixed-point number to an integer, rounding
        /// towards the nearest. Ties are rounded away from zero.
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

        #[cfg(feature = "f16")]
        deprecated_from_float! { fn from_f16(f16) -> $Fixed<Frac> }
        deprecated_from_float! { fn from_f32(f32) -> $Fixed<Frac> }
        deprecated_from_float! { fn from_f64(f64) -> $Fixed<Frac> }

        #[cfg(feature = "f16")]
        deprecated_to_float! { fn to_f16($Fixed) -> f16 }
        deprecated_to_float! { fn to_f32($Fixed) -> f32 }
        deprecated_to_float! { fn to_f64($Fixed) -> f64 }
    };
}
