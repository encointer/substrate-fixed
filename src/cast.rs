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

use crate::{
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use az::{Cast, CheckedCast, OverflowingCast, SaturatingCast, StaticCast, WrappingCast};
use core::mem;
#[cfg(feature = "f16")]
use half::{bf16, f16};

macro_rules! run_time {
    ($Src:ident($LeEqUSrc:ident); $Dst:ident($LeEqUDst:ident)) => {
        impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> Cast<$Dst<FracDst>> for $Src<FracSrc> {
            #[inline]
            fn cast(self) -> $Dst<FracDst> {
                self.to_num()
            }
        }

        impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> CheckedCast<$Dst<FracDst>> for $Src<FracSrc> {
            #[inline]
            fn checked_cast(self) -> Option<$Dst<FracDst>> {
                self.checked_to_num()
            }
        }

        impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> SaturatingCast<$Dst<FracDst>>
            for $Src<FracSrc>
        {
            #[inline]
            fn saturating_cast(self) -> $Dst<FracDst> {
                self.saturating_to_num()
            }
        }

        impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> WrappingCast<$Dst<FracDst>> for $Src<FracSrc> {
            #[inline]
            fn wrapping_cast(self) -> $Dst<FracDst> {
                self.wrapping_to_num()
            }
        }

        impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> OverflowingCast<$Dst<FracDst>>
            for $Src<FracSrc>
        {
            #[inline]
            fn overflowing_cast(self) -> ($Dst<FracDst>, bool) {
                self.overflowing_to_num()
            }
        }
    };

    ($Fixed:ident($LeEqU:ident); $Dst:ident) => {
        impl<Frac: $LeEqU> Cast<$Dst> for $Fixed<Frac> {
            #[inline]
            fn cast(self) -> $Dst {
                self.to_num()
            }
        }

        impl<Frac: $LeEqU> CheckedCast<$Dst> for $Fixed<Frac> {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                self.checked_to_num()
            }
        }

        impl<Frac: $LeEqU> SaturatingCast<$Dst> for $Fixed<Frac> {
            #[inline]
            fn saturating_cast(self) -> $Dst {
                self.saturating_to_num()
            }
        }

        impl<Frac: $LeEqU> WrappingCast<$Dst> for $Fixed<Frac> {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self.wrapping_to_num()
            }
        }

        impl<Frac: $LeEqU> OverflowingCast<$Dst> for $Fixed<Frac> {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                self.overflowing_to_num()
            }
        }
    };

    ($Src:ident; $Fixed:ident($LeEqU:ident)) => {
        impl<Frac: $LeEqU> Cast<$Fixed<Frac>> for $Src {
            #[inline]
            fn cast(self) -> $Fixed<Frac> {
                <$Fixed<Frac>>::from_num(self)
            }
        }

        impl<Frac: $LeEqU> CheckedCast<$Fixed<Frac>> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Fixed<Frac>> {
                <$Fixed<Frac>>::checked_from_num(self)
            }
        }

        impl<Frac: $LeEqU> SaturatingCast<$Fixed<Frac>> for $Src {
            #[inline]
            fn saturating_cast(self) -> $Fixed<Frac> {
                <$Fixed<Frac>>::saturating_from_num(self)
            }
        }

        impl<Frac: $LeEqU> WrappingCast<$Fixed<Frac>> for $Src {
            #[inline]
            fn wrapping_cast(self) -> $Fixed<Frac> {
                <$Fixed<Frac>>::wrapping_from_num(self)
            }
        }

        impl<Frac: $LeEqU> OverflowingCast<$Fixed<Frac>> for $Src {
            #[inline]
            fn overflowing_cast(self) -> ($Fixed<Frac>, bool) {
                <$Fixed<Frac>>::overflowing_from_num(self)
            }
        }
    };
}

macro_rules! compile_time {
    (
        impl<$FracSrc:ident: $LeEqUSrc:ident, $FracDst:ident: $LeEqUDst:ident> StaticCast<$Dst:ty>
            for $Src:ty
        {
            $cond:expr
        }
    ) => {
        impl<$FracSrc: $LeEqUSrc, $FracDst: $LeEqUDst> StaticCast<$Dst> for $Src {
            #[inline]
            fn static_cast(self) -> Option<$Dst> {
                if $cond {
                    Some(az::cast(self))
                } else {
                    None
                }
            }
        }
    };

    (impl<$Frac:ident: $LeEqU:ident> StaticCast<$Dst:ty> for $Src:ty { $cond:expr }) => {
        impl<$Frac: $LeEqU> StaticCast<$Dst> for $Src {
            #[inline]
            fn static_cast(self) -> Option<$Dst> {
                if $cond {
                    Some(az::cast(self))
                } else {
                    None
                }
            }
        }
    };

    ($SrcI:ident, $SrcU:ident($LeEqUSrc:ident); $DstI:ident, $DstU:ident($LeEqUDst:ident)) => {
        compile_time! {
            impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> StaticCast<$DstI<FracDst>>
                for $SrcI<FracSrc>
            {
                <$DstI<FracDst>>::INT_NBITS >= <$SrcI<FracSrc>>::INT_NBITS
            }
        }

        compile_time! {
            impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> StaticCast<$DstU<FracDst>>
                for $SrcI<FracSrc>
            {
                false
            }
        }

        compile_time! {
            impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> StaticCast<$DstI<FracDst>>
                for $SrcU<FracSrc>
            {
                <$DstI<FracDst>>::INT_NBITS > <$SrcU<FracSrc>>::INT_NBITS
            }
        }

        compile_time! {
            impl<FracSrc: $LeEqUSrc, FracDst: $LeEqUDst> StaticCast<$DstU<FracDst>>
                for $SrcU<FracSrc>
            {
                <$DstU<FracDst>>::INT_NBITS >= <$SrcU<FracSrc>>::INT_NBITS
            }
        }
    };

    ($FixedI:ident, $FixedU:ident($LeEqU:ident); int $DstI:ident, $DstU:ident) => {
        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$DstI> for $FixedI<Frac> {
                8 * mem::size_of::<$DstI>() as u32 >= <$FixedI<Frac>>::INT_NBITS
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$DstI> for $FixedU<Frac> {
                8 * mem::size_of::<$DstI>() as u32 > <$FixedU<Frac>>::INT_NBITS
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$DstU> for $FixedI<Frac> {
                false
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$DstU> for $FixedU<Frac> {
                8 * mem::size_of::<$DstU>() as u32 >= <$FixedU<Frac>>::INT_NBITS
            }
        }
    };

    (int $SrcI:ident, $SrcU:ident; $FixedI:ident, $FixedU:ident($LeEqU:ident)) => {
        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedI<Frac>> for $SrcI {
                <$FixedI<Frac>>::INT_NBITS >= 8 * mem::size_of::<$SrcI>() as u32
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedU<Frac>> for $SrcI {
                false
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedI<Frac>> for $SrcU {
                <$FixedI<Frac>>::INT_NBITS > 8 * mem::size_of::<$SrcU>() as u32
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedU<Frac>> for $SrcU {
                <$FixedU<Frac>>::INT_NBITS >= 8 * mem::size_of::<$SrcU>() as u32
            }
        }
    };

    ($Fixed:ident($LeEqU:ident); float $Dst:ident) => {
        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$Dst> for $Fixed<Frac> {
                true
            }
        }
    };

    (float $Src:ident; $Fixed:ident($LeEqU:ident)) => {
        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$Fixed<Frac>> for $Src {
                false
            }
        }
    };
}

macro_rules! run_time_num {
    ($Src:ident($LeEqUSrc:ident); $($Dst:ident($LeEqUDst:ident),)*) => { $(
        run_time! { $Src($LeEqUSrc); $Dst($LeEqUDst) }
    )* };
    ($Fixed:ident($LeEqU:ident); $($Num:ident,)*) => { $(
        run_time! { $Fixed($LeEqU); $Num }
        run_time! { $Num; $Fixed($LeEqU) }
    )* };
    ($($Fixed:ident($LeEqU:ident),)*) => { $(
        run_time_num! {
            $Fixed($LeEqU);
            FixedI8(LeEqU8), FixedI16(LeEqU16), FixedI32(LeEqU32), FixedI64(LeEqU64),
            FixedI128(LeEqU128),
            FixedU8(LeEqU8), FixedU16(LeEqU16), FixedU32(LeEqU32), FixedU64(LeEqU64),
            FixedU128(LeEqU128),
        }
        run_time! { bool; $Fixed($LeEqU) }
        run_time_num! {
            $Fixed($LeEqU);
            i8, i16, i32, i64, i128, isize,
            u8, u16, u32, u64, u128, usize,
            f32, f64,
        }
        #[cfg(feature = "f16")]
        run_time_num! {
            $Fixed($LeEqU);
            f16, bf16,
        }
    )* };
}

run_time_num! {
    FixedI8(LeEqU8), FixedI16(LeEqU16), FixedI32(LeEqU32), FixedI64(LeEqU64), FixedI128(LeEqU128),
    FixedU8(LeEqU8), FixedU16(LeEqU16), FixedU32(LeEqU32), FixedU64(LeEqU64), FixedU128(LeEqU128),
}

macro_rules! compile_time_fixed {
    (
        $SrcI:ident, $SrcU:ident($LeEqUSrc:ident); $(($DstI:ident, $DstU:ident($LeEqUDst:ident)),)*
    ) => { $(
        compile_time! { $SrcI, $SrcU($LeEqUSrc); $DstI, $DstU($LeEqUDst) }
    )* };
    ($($FixedI:ident, $FixedU:ident($LeEqU:ident),)*) => { $(
        compile_time_fixed! {
            $FixedI, $FixedU($LeEqU);
            (FixedI8, FixedU8(LeEqU8)),
            (FixedI16, FixedU16(LeEqU16)),
            (FixedI32, FixedU32(LeEqU32)),
            (FixedI64, FixedU64(LeEqU64)),
            (FixedI128, FixedU128(LeEqU128)),
        }
    )* };
}

compile_time_fixed! {
    FixedI8, FixedU8(LeEqU8),
    FixedI16, FixedU16(LeEqU16),
    FixedI32, FixedU32(LeEqU32),
    FixedI64, FixedU64(LeEqU64),
    FixedI128, FixedU128(LeEqU128),
}

macro_rules! compile_time_int {
    ($FixedI:ident, $FixedU:ident($LeEqU:ident); $(($IntI:ident, $IntU:ident),)*) => { $(
        compile_time! { $FixedI, $FixedU($LeEqU); int $IntI, $IntU }
        compile_time! { int $IntI, $IntU; $FixedI, $FixedU($LeEqU) }
    )* };
    ($($FixedI:ident, $FixedU:ident($LeEqU:ident),)*) => { $(
        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedI<Frac>> for bool {
                <$FixedI<Frac>>::INT_NBITS > 1
            }
        }

        compile_time! {
            impl<Frac: $LeEqU> StaticCast<$FixedU<Frac>> for bool {
                <$FixedU<Frac>>::INT_NBITS >= 1
            }
        }

        compile_time_int! {
            $FixedI, $FixedU($LeEqU);
            (i8, u8),
            (i16, u16),
            (i32, u32),
            (i64, u64),
            (i128, u128),
            (isize, usize),
        }
    )* };
}

compile_time_int! {
    FixedI8, FixedU8(LeEqU8),
    FixedI16, FixedU16(LeEqU16),
    FixedI32, FixedU32(LeEqU32),
    FixedI64, FixedU64(LeEqU64),
    FixedI128, FixedU128(LeEqU128),
}

macro_rules! compile_time_float {
    ($Fixed:ident($LeEqU:ident); $($Float:ident,)*) => { $(
        compile_time! { $Fixed($LeEqU); float $Float }
        compile_time! { float $Float; $Fixed($LeEqU) }
    )* };
    ($($Fixed:ident($LeEqU:ident),)*) => { $(
        compile_time_float! {
            $Fixed($LeEqU);
            f32, f64,
        }
        #[cfg(feature = "f16")]
        compile_time_float! {
            $Fixed($LeEqU);
            f16, bf16,
        }
    )* };
}

compile_time_float! {
    FixedI8(LeEqU8), FixedI16(LeEqU16), FixedI32(LeEqU32), FixedI64(LeEqU64), FixedI128(LeEqU128),
    FixedU8(LeEqU8), FixedU16(LeEqU16), FixedU32(LeEqU32), FixedU64(LeEqU64), FixedU128(LeEqU128),
}
