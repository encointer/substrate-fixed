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

macro_rules! fixed_checked_arith {
    ($Fixed:ident($Inner:ty), $Signedness:tt) => {
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
    };
}
