// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Operations and constants for 32-bits floats (`f32` type)

#![allow(overflowing_literals)]

/// The radix or base of the internal representation of `f32`.
pub const RADIX: u32 = 2;

/// Number of significant digits in base 2.
pub const MANTISSA_DIGITS: u32 = 24;
/// Approximate number of significant digits in base 10.
pub const DIGITS: u32 = 6;

/// Difference between `1.0` and the next largest representable number.
pub const EPSILON: f32 = 1.19209290e-07_f32;

/// Smallest finite `f32` value.
pub const MIN: f32 = -3.40282347e+38_f32;
/// Smallest positive normal `f32` value.
pub const MIN_POSITIVE: f32 = 1.17549435e-38_f32;
/// Largest finite `f32` value.
pub const MAX: f32 = 3.40282347e+38_f32;

/// One greater than the minimum possible normal power of 2 exponent.
pub const MIN_EXP: i32 = -125;
/// Maximum possible power of 2 exponent.
pub const MAX_EXP: i32 = 128;

/// Minimum possible normal power of 10 exponent.
pub const MIN_10_EXP: i32 = -37;
/// Maximum possible power of 10 exponent.
pub const MAX_10_EXP: i32 = 38;

/// Not a Number (NaN).
pub const NAN: f32 = 0.0_f32 / 0.0_f32;
/// Infinity (∞).
pub const INFINITY: f32 = 1.0_f32 / 0.0_f32;
/// Negative infinity (-∞).
pub const NEG_INFINITY: f32 = -1.0_f32 / 0.0_f32;

/// Basic mathematical constants.
pub mod consts {
    // FIXME: replace with mathematical constants from cmath.

    /// Archimedes' constant (π)    
    pub const PI: f32 = 3.14159265358979323846264338327950288_f32;

    /// π/2    
    pub const FRAC_PI_2: f32 = 1.57079632679489661923132169163975144_f32;

    /// π/3    
    pub const FRAC_PI_3: f32 = 1.04719755119659774615421446109316763_f32;

    /// π/4    
    pub const FRAC_PI_4: f32 = 0.785398163397448309615660845819875721_f32;

    /// π/6    
    pub const FRAC_PI_6: f32 = 0.52359877559829887307710723054658381_f32;

    /// π/8    
    pub const FRAC_PI_8: f32 = 0.39269908169872415480783042290993786_f32;

    /// 1/π    
    pub const FRAC_1_PI: f32 = 0.318309886183790671537767526745028724_f32;

    /// 2/π    
    pub const FRAC_2_PI: f32 = 0.636619772367581343075535053490057448_f32;

    /// 2/sqrt(π)    
    pub const FRAC_2_SQRT_PI: f32 = 1.12837916709551257389615890312154517_f32;

    /// sqrt(2)    
    pub const SQRT_2: f32 = 1.41421356237309504880168872420969808_f32;

    /// 1/sqrt(2)    
    pub const FRAC_1_SQRT_2: f32 = 0.707106781186547524400844362104849039_f32;

    /// Euler's number (e)    
    pub const E: f32 = 2.71828182845904523536028747135266250_f32;

    /// log<sub>2</sub>(e)    
    pub const LOG2_E: f32 = 1.44269504088896340735992468100189214_f32;

    /// log<sub>10</sub>(e)    
    pub const LOG10_E: f32 = 0.434294481903251827651128918916605082_f32;

    /// ln(2)    
    pub const LN_2: f32 = 0.693147180559945309417232121458176568_f32;

    /// ln(10)    
    pub const LN_10: f32 = 2.30258509299404568401799145468436421_f32;
}
