//  Copyright (c) 2019 Alain Brenzikofer
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.

/*!
This module contains transcendental functions.
*/
use crate::consts;
use crate::traits::{Fixed, FixedSigned, LossyFrom, ToFixed};
use crate::types::{I9F23, I9F55, U0F128};
use core::ops::{AddAssign, BitOrAssign, ShlAssign};

type ConstType = I9F23;

/// zero
pub const ZERO: I9F23 = I9F23::from_bits(0i32 << 23);
/// one
pub const ONE: I9F23 = I9F23::from_bits(1i32 << 23);
/// two
pub const TWO: I9F23 = I9F23::from_bits(2i32 << 23);
/// three
pub const THREE: I9F23 = I9F23::from_bits(3i32 << 23);
/// 2*pi
pub const TWO_PI: I9F23 = I9F23::from_bits((consts::PI.to_bits() >> 102) as i32);
/// pi
pub const PI: I9F23 = I9F23::from_bits((consts::PI.to_bits() >> 103) as i32);
/// pi/2
pub const FRAC_PI_2: I9F23 = I9F23::from_bits((consts::PI.to_bits() >> 104) as i32);
/// pi/4
pub const FRAC_PI_4: I9F23 = I9F23::from_bits((consts::PI.to_bits() >> 105) as i32);
/// log2(e)
pub const LOG2_E: I9F23 = I9F23::from_bits((consts::LOG2_E.to_bits() >> 104) as i32);
/// e
pub const E: I9F23 = I9F23::from_bits((consts::E.to_bits() >> 103) as i32);

// generate with
// ```matlab
// for i = [0:63]
//   disp(["0x", dec2hex(round(atan(2^(-i)) * 2^128),32)])
// end
// ```
/// arctan(2^-i) lookup table for cordic
const ARCTAN_ANGLES: [U0F128; 64] = [
    U0F128::from_bits(0xC90FDAA22168C0000000000000000000),
    U0F128::from_bits(0x76B19C1586ED3C000000000000000000),
    U0F128::from_bits(0x3EB6EBF25901BA000000000000000000),
    U0F128::from_bits(0x1FD5BA9AAC2F6E000000000000000000),
    U0F128::from_bits(0x0FFAADDB967EF5000000000000000000),
    U0F128::from_bits(0x07FF556EEA5D89400000000000000000),
    U0F128::from_bits(0x03FFEAAB776E53600000000000000000),
    U0F128::from_bits(0x01FFFD555BBBA9700000000000000000),
    U0F128::from_bits(0x00FFFFAAAADDDDB80000000000000000),
    U0F128::from_bits(0x007FFFF55556EEF00000000000000000),
    U0F128::from_bits(0x003FFFFEAAAAB7780000000000000000),
    U0F128::from_bits(0x001FFFFFD55555BC0000000000000000),
    U0F128::from_bits(0x000FFFFFFAAAAAAE0000000000000000),
    U0F128::from_bits(0x0007FFFFFF5555558000000000000000),
    U0F128::from_bits(0x0003FFFFFFEAAAAAA000000000000000),
    U0F128::from_bits(0x0001FFFFFFFD55555000000000000000),
    U0F128::from_bits(0x0000FFFFFFFFAAAAA800000000000000),
    U0F128::from_bits(0x00007FFFFFFFF5555400000000000000),
    U0F128::from_bits(0x00003FFFFFFFFEAAAA00000000000000),
    U0F128::from_bits(0x00001FFFFFFFFFD55500000000000000),
    U0F128::from_bits(0x00000FFFFFFFFFFAAA80000000000000),
    U0F128::from_bits(0x000007FFFFFFFFFF5540000000000000),
    U0F128::from_bits(0x000003FFFFFFFFFFEAA0000000000000),
    U0F128::from_bits(0x000001FFFFFFFFFFFD50000000000000),
    U0F128::from_bits(0x000000FFFFFFFFFFFFA8000000000000),
    U0F128::from_bits(0x0000007FFFFFFFFFFFF4000000000000),
    U0F128::from_bits(0x0000003FFFFFFFFFFFFE000000000000),
    U0F128::from_bits(0x00000020000000000000000000000000),
    U0F128::from_bits(0x00000010000000000000000000000000),
    U0F128::from_bits(0x00000008000000000000000000000000),
    U0F128::from_bits(0x00000004000000000000000000000000),
    U0F128::from_bits(0x00000002000000000000000000000000),
    U0F128::from_bits(0x00000001000000000000000000000000),
    U0F128::from_bits(0x00000000800000000000000000000000),
    U0F128::from_bits(0x00000000400000000000000000000000),
    U0F128::from_bits(0x00000000200000000000000000000000),
    U0F128::from_bits(0x00000000100000000000000000000000),
    U0F128::from_bits(0x00000000080000000000000000000000),
    U0F128::from_bits(0x00000000040000000000000000000000),
    U0F128::from_bits(0x00000000020000000000000000000000),
    U0F128::from_bits(0x00000000010000000000000000000000),
    U0F128::from_bits(0x00000000008000000000000000000000),
    U0F128::from_bits(0x00000000004000000000000000000000),
    U0F128::from_bits(0x00000000002000000000000000000000),
    U0F128::from_bits(0x00000000001000000000000000000000),
    U0F128::from_bits(0x00000000000800000000000000000000),
    U0F128::from_bits(0x00000000000400000000000000000000),
    U0F128::from_bits(0x00000000000200000000000000000000),
    U0F128::from_bits(0x00000000000100000000000000000000),
    U0F128::from_bits(0x00000000000080000000000000000000),
    U0F128::from_bits(0x00000000000040000000000000000000),
    U0F128::from_bits(0x00000000000020000000000000000000),
    U0F128::from_bits(0x00000000000010000000000000000000),
    U0F128::from_bits(0x00000000000008000000000000000000),
    U0F128::from_bits(0x00000000000004000000000000000000),
    U0F128::from_bits(0x00000000000002000000000000000000),
    U0F128::from_bits(0x00000000000001000000000000000000),
    U0F128::from_bits(0x00000000000000800000000000000000),
    U0F128::from_bits(0x00000000000000400000000000000000),
    U0F128::from_bits(0x00000000000000200000000000000000),
    U0F128::from_bits(0x00000000000000100000000000000000),
    U0F128::from_bits(0x00000000000000080000000000000000),
    U0F128::from_bits(0x00000000000000040000000000000000),
    U0F128::from_bits(0x00000000000000020000000000000000),
];

/// right-shift with rounding
fn rs<T>(operand: T) -> T
where
    T: Fixed,
{
    let lsb = T::from_num(1) >> T::frac_nbits();
    (operand >> 1) + (operand & lsb)
    //let x = operand.to_bits();
    //T::from_bits((x >> 1) + (x & 1))
}

/// square root
pub fn sqrt<S, D>(operand: S) -> Result<D, &'static str>
where
    S: Fixed + PartialOrd<ConstType>,
    D: Fixed + PartialOrd<ConstType> + From<S>,
{
    let mut invert = false;
    if operand < ZERO {
        return Err("Can't calculate sqrt from negative numbers.");
    };

    let mut operand = D::from(operand);
    if operand == ZERO || operand == ONE {
        return Ok(operand);
    };
    if operand < ONE {
        invert = true;
        operand = if let Some(r) = D::from_num(1).checked_div(operand) {
            r
        } else {
            return Err("Overflow inverting operand.");
        };
    }
    // Newton iterations
    let mut l = (operand / D::from_num(2)) + D::from_num(1);
    for _i in 0..D::frac_nbits() {
        l = (l + operand / l) / D::from_num(2);
    }
    if invert {
        l = if let Some(r) = D::from_num(1).checked_div(l) {
            r
        } else {
            return Err("Overflow un-inverting operand.");
        };
    }
    Ok(l)
}

/// base 2 logarithm assuming self >=1
fn log2_inner<S, D>(operand: S) -> D
where
    S: FixedSigned + PartialOrd<ConstType>,
    D: FixedSigned,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    let mut x = operand;
    let mut result = D::from_num(0).to_bits();
    let lsb = (D::from_num(1) >> D::frac_nbits()).to_bits();

    while x >= TWO {
        result += lsb;
        x = rs(x);
    }

    if x == ONE {
        return D::from_num(result);
    };

    for _i in (0..D::frac_nbits()).rev() {
        x *= x;
        result <<= lsb;
        if x >= TWO {
            result |= lsb;
            x = rs(x);
        }
    }
    D::from_bits(result)
}

/// base 2 logarithm
pub fn log2<S, D>(operand: S) -> Result<D, ()>
where
    S: FixedSigned + PartialOrd<ConstType>,
    D: FixedSigned + PartialOrd<ConstType> + From<S>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    if operand <= S::from_num(0) {
        return Err(());
    };

    let operand = D::from(operand);
    if operand < D::from_num(1) {
        let inverse = D::from_num(1).checked_div(operand).unwrap();
        return Ok(-log2_inner::<D, D>(inverse));
    };
    return Ok(log2_inner::<D, D>(operand));
}

/// natural logarithm
pub fn ln<S, D>(operand: S) -> Result<D, ()>
where
    S: FixedSigned + PartialOrd<ConstType>,
    D: FixedSigned + PartialOrd<ConstType> + From<S> + From<ConstType>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    Ok(log2::<S, D>(operand)? / D::from(LOG2_E))
}

/// exponential function e^(operand)
pub fn exp<S, D>(mut operand: S) -> Result<D, ()>
where
    S: FixedSigned + PartialOrd<ConstType>,
    D: FixedSigned + PartialOrd<ConstType> + From<S> + From<ConstType>,
{
    if operand == ZERO {
        return Ok(D::from_num(1));
    };
    if operand == ONE {
        return Ok(D::from(E));
    };
    let neg = operand < ZERO;
    if neg {
        operand = -operand;
    };

    let operand = D::from(operand);
    let mut result = operand + D::from_num(1);
    let mut term = operand;

    for i in 2..D::frac_nbits() {
        term = if let Some(r) = term.checked_mul(operand) {
            r
        } else {
            return Err(());
        };
        //let bits = if let Some(r) = D::from_num(i)
        //    { r } else { return Err(()) };
        term = if let Some(r) = term.checked_div(D::from_num(i)) {
            r
        } else {
            return Err(());
        };

        result = if let Some(r) = result.checked_add(term) {
            r
        } else {
            return Err(());
        };
        //if term < 500 && (i > 15 || term < $ty(20i32).unwrap()) {
        //    break;
        //};
    }
    if neg {
        result = if let Some(r) = D::from_num(1).checked_div(result) {
            r
        } else {
            return Err(());
        };
    }
    Ok(result)
}

/// power
pub fn pow<S, D>(operand: S, exponent: S) -> Result<D, ()>
where
    S: FixedSigned + PartialOrd<ConstType>,
    D: FixedSigned + PartialOrd<ConstType> + From<S> + From<ConstType>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    // TODO: dynamic typing depending on input
    //type I = FixedI128<U64>; // internal
    if operand == S::from_num(0) {
        return Ok(D::from_num(0));
    };
    if exponent == S::from_num(0) {
        return Ok(D::from_num(1));
    };
    if exponent == S::from_num(1) {
        return Ok(D::from(operand));
    };

    let r = if let Some(r) = ln::<S, D>(operand)?.checked_mul(exponent.into()) {
        r
    } else {
        return Err(());
    };
    let result: D = if let Ok(r) = exp(r) {
        r
    } else {
        return Err(());
    };
    let (result, oflw) = result.overflowing_to_num::<D>();
    if oflw {
        return Err(());
    };
    Ok(result)
}

/// power with integer exponend
pub fn powi<S,D>(operand: S, exponent: i32) -> Result<D, ()>
where
    S: Fixed + PartialOrd<ConstType>,
    D: Fixed + PartialOrd<ConstType> + From<S> + From<ConstType>,
    D::Bits: Copy + ToFixed + AddAssign + BitOrAssign + ShlAssign,
{
    if operand == S::from_num(0) {
        return Ok(D::from_num(0));
    };
    if exponent == 0 {
        return Ok(D::from_num(1));
    };
    if exponent == 1 {
        return Ok(D::from(operand));
    };
    let operand = D::from(operand);
    let mut r = operand;

    for _i in 1..exponent.abs() {
        r = if let Some(r) = r.checked_mul(operand) {
            r
        } else {
            return Err(());
        };
    }
    if exponent < 0 {
        r = if let Some(r) = D::from_num(1).checked_div(r) {
            r
        } else {
            return Err(());
        };
    }
    Ok(r)
}

/// CORDIC in rotation mode.
fn cordic_rotation<T>(mut x: T, mut y: T, mut z: T) -> (T, T)
where
    T: FixedSigned + PartialOrd<ConstType> + LossyFrom<U0F128>,
{
    for (angle, i) in ARCTAN_ANGLES.iter().cloned().zip(0..) {
        let angle = T::lossy_from(angle);
        //if z == ZERO {
        //    break;
        //};
        if i >= 24 {
            break;
        }
        let prev_x = x;
        if z < ZERO {
            x += y >> i;
            y -= prev_x >> i;
            z += angle;
        } else {
            x -= y >> i;
            y += prev_x >> i;
            z -= angle;
        }
    }
    (x, y)
}

/// sine function in radians
pub fn sin<T>(mut angle: T) -> T
where
    T: FixedSigned
        + PartialOrd<ConstType>
        + LossyFrom<ConstType>
        + LossyFrom<I9F23>
        + LossyFrom<U0F128>,
{
    //wraparound
    while angle > PI {
        angle -= T::lossy_from(TWO_PI);
    }
    while angle < -PI {
        angle += T::lossy_from(TWO_PI);
    }
    //mirror
    if angle > FRAC_PI_2 {
        angle = T::lossy_from(FRAC_PI_2) - (angle - T::lossy_from(FRAC_PI_2));
    }
    if angle < -FRAC_PI_2 {
        angle = -T::lossy_from(FRAC_PI_2) - (angle + T::lossy_from(FRAC_PI_2));
    }

    //FIXME: find correction factor for constant iterations
    // now this is optimized for I32F32 type
    // x0= 1/K with K ~ 1.647 for infinite iterations
    // dec2hex(round(1 / 1.6467602578923106 * 2^128),32)
    let x = T::lossy_from(U0F128::from_bits(0x9B74EDA8A01E20000000000000000000));
    //let x = T::from_num(1);
    let (_x, y) = cordic_rotation(x, T::from_num(0), angle);
    y
}

/// cosine function in radians
pub fn cos<T>(angle: T) -> T
where
    T: FixedSigned
        + PartialOrd<ConstType>
        + LossyFrom<ConstType>
        + LossyFrom<I9F55>
        + LossyFrom<U0F128>,
{
    sin(angle + T::lossy_from(FRAC_PI_2))
}

/// tangent function in radians
pub fn tan<T>(mut angle: T) -> T
where
    T: FixedSigned
        + PartialOrd<ConstType>
        + LossyFrom<ConstType>
        + LossyFrom<I9F55>
        + LossyFrom<U0F128>,
{
    angle *= T::from_num(2);
    sin(angle) / (T::from_num(1) + cos(angle))
}

/// arcsine function in radians
//FIXME: only valid for very small angles
pub fn asin<T>(angle: T) -> T {
    angle
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::LossyInto;
    use crate::types::{I32F32, I64F64, U64F64};

    #[test]
    fn sqrt_works() {
        {
            type S = I9F23;
            type D = I9F23;

            assert_eq!(sqrt::<S, D>(S::from_num(4)).unwrap(), TWO);

            let result: f64 = sqrt::<S, D>(S::from_num(1)).unwrap().lossy_into();
            assert_relative_eq!(result, 1.0, epsilon = 1.0e-6);
            let result: f64 = sqrt::<S, D>(S::from_num(0)).unwrap().lossy_into();
            assert_relative_eq!(result, 0.0, epsilon = 1.0e-6);
            let result: f64 = sqrt::<S, D>(S::from_num(0.1_f32)).unwrap().lossy_into();
            assert_relative_eq!(result, 0.316228, epsilon = 1.0e-4);
            let result: f64 = sqrt::<S, D>(S::from_num(10)).unwrap().lossy_into();
            assert_relative_eq!(result, 3.16228, epsilon = 1.0e-4);
        }
        {
            type S = U64F64;
            type D = U64F64;
            let result: f64 = sqrt::<S, D>(S::from_num(1)).unwrap().lossy_into();
            assert_relative_eq!(result, 1.0, epsilon = 1.0e-6);
        }
    }

    #[test]
    fn sqrt_check_lower_bound_of_working_values() {
        // Todo: This could be done for other types too.
        type S = I32F32;
        type D = I32F32;

        // this works
        let result: f64 = sqrt::<S, D>(S::from_num(5.8208e-10)).unwrap().lossy_into();
        assert_relative_eq!(result, 0.0000261, epsilon = 1.0e-6);

        // slightly below lower bound that produces an overflow
        let res = sqrt::<S, D>(S::from_num(5.8205e-10));
        assert_eq!(res.unwrap_err(), "Overflow inverting operand.")
    }

    #[test]
    fn rs_works() {
        let result: f64 = rs(I9F23::from_num(0)).lossy_into();
        assert_eq!(result, 0.0);
        let result: f64 = rs(I9F23::from_num(1)).lossy_into();
        assert_eq!(result, 0.5);
        let result: f64 = rs(I9F23::from_num(2)).lossy_into();
        assert_eq!(result, 1.0);
        let result: f64 = rs(I9F23::from_num(3)).lossy_into();
        assert_eq!(result, 1.5);
        let result: f64 = rs(I9F23::from_num(4)).lossy_into();
        assert_eq!(result, 2.0);
        let result: f64 = rs(I9F23::from_num(-1)).lossy_into();
        assert_eq!(result, -0.5);
        let result: f64 = rs(I9F23::from_num(-2)).lossy_into();
        assert_eq!(result, -1.0);

        assert_eq!(rs(I9F23::from_bits(1)).to_bits(), 1);
        assert_eq!(rs(I9F23::from_bits(2)).to_bits(), 1);
        assert_eq!(rs(I9F23::from_bits(3)).to_bits(), 2);
        assert_eq!(rs(I9F23::from_bits(4)).to_bits(), 2);
    }

    #[test]
    fn log2_works() {
        type S = I9F23;
        type D = I32F32;
        assert!(log2::<S, D>(S::from_num(0)).is_err());

        assert_eq!(log2::<S, D>(S::from_num(1)).unwrap(), ZERO);

        let result: D = log2::<S, D>(S::from_num(2)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 1.0, epsilon = 1.0e-6);
        let result: D = log2::<S, D>(S::from_num(4)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 2.0, epsilon = 1.0e-6);
        let result: D = log2::<S, D>(S::from_num(3.33333_f64)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 1.73696, epsilon = 1.0e-5);
        let result: D = log2::<S, D>(S::from_num(0.11111_f64)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, -3.16994, epsilon = 1.0e-2);
    }

    #[test]
    fn ln_works() {
        type S = I9F23;
        type D = I32F32;
        assert!(ln::<S, D>(S::from_num(0)).is_err());
        assert_eq!(ln::<S, D>(S::from_num(1)).unwrap(), ZERO);
        let result: f64 = ln::<S, D>(E).unwrap().lossy_into();
        assert_relative_eq!(result, 1.0, epsilon = 1.0e-4);
        let result: f64 = ln::<S, D>(S::from_num(10)).unwrap().lossy_into();
        assert_relative_eq!(result, 2.30259, epsilon = 1.0e-4);
        let result: f64 = ln::<S, D>(S::from_num(0.00001)).unwrap().lossy_into();
        assert_relative_eq!(result, -11.5129, epsilon = 1.0e-1);
    }

    #[test]
    fn exp_works() {
        type S = I9F23;
        type D = I32F32;

        let result: f64 = exp::<S, D>(ZERO).unwrap().lossy_into();
        assert_eq!(result, 1.0);

        let result: f64 = exp::<S, D>(ONE).unwrap().lossy_into();
        assert_relative_eq!(result, 2.718281828459045235_f64, epsilon = 1.0e-4);

        let result: f64 = exp::<S, D>(S::from_num(5.0)).unwrap().lossy_into();
        assert_relative_eq!(result, 148.413159, epsilon = 1.0e-1);
        // overflow if type too small
        assert!(exp::<S, D>(S::from_num(-23)).is_err());
        // same is fine with larger destination type
        let result: f64 = exp::<S, I64F64>(S::from_num(-23)).unwrap().lossy_into();
        assert_relative_eq!(result, 102.619e-12, epsilon = 1.0e-12);
    }

    #[test]
    fn pow_works() {
        type S = I9F23;
        type D = I32F32;

        let result: D = pow(ZERO, TWO).unwrap();
        let result: f64 = result.lossy_into();
        assert_eq!(result, 0.0);

        let result: D = pow(ONE, TWO).unwrap();
        let result: f64 = result.lossy_into();
        assert_eq!(result, 1.0);

        let result: D = pow(TWO, TWO).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 4.0, epsilon = 1.0e-3);
        let result: D = pow(TWO, THREE).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 8.0, epsilon = 1.0e-3);
        let result: D = pow(S::from_num(2.9), S::from_num(3.1)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 27.129, epsilon = 1.0e-2);
        let result: D = pow(S::from_num(0.0001), S::from_num(2)).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 0.00000001, epsilon = 1.0e-9);

        // this would lead a complex result due to computation method
        assert!(pow::<S, D>(S::from_num(-0.0001), S::from_num(2)).is_err());
    }

    #[test]
    fn powi_works() {
        type D = I32F32;

        let result: D = powi(ZERO, 2).unwrap();
        let result: f64 = result.lossy_into();
        assert_eq!(result, 0.0);

        let result: D = powi(ONE, 2).unwrap();
        let result: f64 = result.lossy_into();
        assert_eq!(result, 1.0);

        let result: D = powi(TWO, 2).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 4.0, epsilon = 1.0e-3);

        let result: D = powi(TWO, -2).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 1.0 / 4.0, epsilon = 1.0e-4);

        let result: D = powi(TWO, 3).unwrap();
        let result: f64 = result.lossy_into();
        assert_relative_eq!(result, 8.0, epsilon = 1.0e-3);
    }

    #[test]
    fn sin_works() {
        // for correction factor reference
        let result: f64 = sin(I32F32::lossy_from(FRAC_PI_2)).lossy_into();
        assert_relative_eq!(result, 1.0, epsilon = 1.0e-5);

        let result: f64 = sin(FRAC_PI_2).lossy_into();
        assert_relative_eq!(result, 1.0, epsilon = 1.0e-5);

        let result: f64 = sin(I32F32::from_num(0)).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);
        let result: f64 = sin(I9F23::from_num(0)).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);
        let result: f64 = sin(PI).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);
        let result: f64 = sin(PI + FRAC_PI_2).lossy_into();
        assert_relative_eq!(result, -1.0, epsilon = 1.0e-5);
        let result: f64 = sin(TWO_PI).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);
        let result: f64 = sin(FRAC_PI_4).lossy_into();
        assert_relative_eq!(result, 0.707107, epsilon = 1.0e-1);
        let result: f64 = sin(-FRAC_PI_2).lossy_into();
        assert_relative_eq!(result, -1.0, epsilon = 1.0e-1);
        let result: f64 = sin(-FRAC_PI_4).lossy_into();
        assert_relative_eq!(result, -0.707107, epsilon = 1.0e-1);
        let result: f64 = sin(PI + FRAC_PI_4).lossy_into();
        assert_relative_eq!(result, -0.707107, epsilon = 1.0e-1);
        let result: f64 = sin(TWO).lossy_into();
        assert_relative_eq!(result, 0.909297, epsilon = 1.0e-5);
        let result: f64 = sin(-TWO).lossy_into();
        assert_relative_eq!(result, -0.909297, epsilon = 1.0e-5);
    }

    #[test]
    fn cos_works() {
        let result: f64 = cos(I9F23::from_num(0)).lossy_into();
        assert_relative_eq!(result, 1.0, epsilon = 1.0e-5);
    }

    #[test]
    fn tan_works() {
        let result: f64 = tan(I9F23::from_num(0)).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);

        let result: f64 = tan(ONE).lossy_into();
        assert_relative_eq!(result, 1.55741, epsilon = 1.0e-5);
    }

    #[test]
    fn asin_works() {
        let result: f64 = asin(I9F23::from_num(0)).lossy_into();
        assert_relative_eq!(result, 0.0, epsilon = 1.0e-5);
        let result: f64 = asin(I9F23::from_num(0.01)).lossy_into();
        assert_relative_eq!(result, 0.01, epsilon = 1.0e-5);
    }
}
