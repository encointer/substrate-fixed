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

macro_rules! fixed_deprecated {
    ($Fixed:ident($Inner:ty)) => {
        /// Creates a fixed-point number from another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by from_num")]
        pub fn from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::from_num(src)
        }

        /// Converts a fixed-point number to another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by to_num")]
        pub fn to_fixed<Dst: FromFixed>(self) -> Dst {
            self.to_num()
        }

        /// Creates a fixed-point number from another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by from_num")]
        pub fn from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::from_num(src)
        }

        /// Converts a fixed-point number to another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by to_num")]
        pub fn to_int<Dst: FromFixed>(self) -> Dst {
            self.to_num()
        }

        /// Creates a fixed-point number from another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by from_num")]
        pub fn from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::from_num(src)
        }

        /// Converts a fixed-point number to another number.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by to_num")]
        pub fn to_float<Dst: FromFixed>(self) -> Dst {
            self.to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by checked_from_num")]
        pub fn checked_from_fixed<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
            Self::checked_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by checked_to_num")]
        pub fn checked_to_fixed<Dst: FromFixed>(self) -> Option<Dst> {
            self.checked_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by checked_from_num")]
        pub fn checked_from_int<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
            Self::checked_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by checked_to_num")]
        pub fn checked_to_int<Dst: FromFixed>(self) -> Option<Dst> {
            self.checked_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by checked_from_num")]
        pub fn checked_from_float<Src: ToFixed>(src: Src) -> Option<$Fixed<Frac>> {
            Self::checked_from_num(src)
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by saturating_from_num")]
        pub fn saturating_from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::saturating_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by saturating_to_num")]
        pub fn saturating_to_fixed<Dst: FromFixed>(self) -> Dst {
            self.saturating_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by saturating_from_num")]
        pub fn saturating_from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::saturating_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by saturating_to_num")]
        pub fn saturating_to_int<Dst: FromFixed>(self) -> Dst {
            self.saturating_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by saturating_from_num")]
        pub fn saturating_from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::saturating_from_num(src)
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by wrapping_from_num")]
        pub fn wrapping_from_fixed<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::wrapping_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by wrapping_to_num")]
        pub fn wrapping_to_fixed<Dst: FromFixed>(self) -> Dst {
            self.wrapping_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by wrapping_from_num")]
        pub fn wrapping_from_int<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::wrapping_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by wrapping_to_num")]
        pub fn wrapping_to_int<Dst: FromFixed>(self) -> Dst {
            self.wrapping_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by wrapping_from_num")]
        pub fn wrapping_from_float<Src: ToFixed>(src: Src) -> $Fixed<Frac> {
            Self::wrapping_from_num(src)
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by overflowing_from_num")]
        pub fn overflowing_from_fixed<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
            Self::overflowing_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by overflowing_to_num")]
        pub fn overflowing_to_fixed<Dst: FromFixed>(self) -> (Dst, bool) {
            self.overflowing_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by overflowing_from_num")]
        pub fn overflowing_from_int<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
            Self::overflowing_from_num(src)
        }

        /// Converts a fixed-point number to another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by overflowing_to_num")]
        pub fn overflowing_to_int<Dst: FromFixed>(self) -> (Dst, bool) {
            self.overflowing_to_num()
        }

        /// Creates a fixed-point number from another number if it fits.
        #[inline]
        #[deprecated(since = "0.4.2", note = "replaced by overflowing_from_num")]
        pub fn overflowing_from_float<Src: ToFixed>(src: Src) -> ($Fixed<Frac>, bool) {
            Self::overflowing_from_num(src)
        }
    };
}
