// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::marker::Sized;

/// The `Add` trait is used to specify the functionality of `+`.
///
/// # Examples
///
/// This example creates a `Point` struct that implements the `Add` trait, and
/// then demonstrates adding two `Point`s.
///
/// ```
/// use std_spirv::ops::Add;
///
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl Add for Point {
///     type Output = Point;
///
///     fn add(self, other: Point) -> Point {
///         Point {
///             x: self.x + other.x,
///             y: self.y + other.y,
///         }
///     }
/// }
///
/// impl PartialEq for Point {
///     fn eq(&self, other: &Self) -> bool {
///         self.x == other.x && self.y == other.y
///     }
/// }
///
/// fn main() {
///     assert_eq!(Point { x: 1, y: 0 } + Point { x: 2, y: 3 },
///                Point { x: 3, y: 3 });
/// }
/// ```
///
#[lang = "add"]
pub trait Add<RHS = Self> {
    /// The resulting type after applying the `+` operator
    type Output;

    /// The method for the `+` operator
    fn add(self, rhs: RHS) -> Self::Output;
}

macro_rules! add_impl {
    ($($t:ty)*) => ($(
        impl Add for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn add(self, other: $t) -> $t { self + other }
        }
    )*)
}

add_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `Sub` trait is used to specify the functionality of `-`.
///
/// # Examples
///
/// This example creates a `Point` struct that implements the `Sub` trait, and
/// then demonstrates subtracting two `Point`s.
///
/// ```
/// use std_spirv::ops::Sub;
///
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl Sub for Point {
///     type Output = Point;
///
///     fn sub(self, other: Point) -> Point {
///         Point {
///             x: self.x - other.x,
///             y: self.y - other.y,
///         }
///     }
/// }
///
/// impl PartialEq for Point {
///     fn eq(&self, other: &Self) -> bool {
///         self.x == other.x && self.y == other.y
///     }
/// }
///
/// fn main() {
///     assert_eq!(Point { x: 3, y: 3 } - Point { x: 2, y: 3 },
///                Point { x: 1, y: 0 });
/// }
/// ```
///
#[lang = "sub"]
pub trait Sub<RHS=Self> {
    /// The resulting type after applying the `-` operator
    type Output;

    /// The method for the `-` operator
    fn sub(self, rhs: RHS) -> Self::Output;
}

macro_rules! sub_impl {
    ($($t:ty)*) => ($(
        impl Sub for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn sub(self, other: $t) -> $t { self - other }
        }
    )*)
}

sub_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `Mul` trait is used to specify the functionality of `*`.
///
/// # Examples
///
/// Implementing a `Mul`tipliable rational number struct:
///
/// ```
/// use std::ops::Mul;
///
/// // The uniqueness of rational numbers in lowest terms is a consequence of
/// // the fundamental theorem of arithmetic.
/// #[derive(Eq)]
/// #[derive(PartialEq, Debug)]
/// struct Rational {
///     nominator: usize,
///     denominator: usize,
/// }
///
/// impl Rational {
///     fn new(nominator: usize, denominator: usize) -> Self {
///         if denominator == 0 {
///             panic!("Zero is an invalid denominator!");
///         }
///
///         // Reduce to lowest terms by dividing by the greatest common
///         // divisor.
///         let gcd = gcd(nominator, denominator);
///         Rational {
///             nominator: nominator / gcd,
///             denominator: denominator / gcd,
///         }
///     }
/// }
///
/// impl Mul for Rational {
///     // The multiplication of rational numbers is a closed operation.
///     type Output = Self;
///
///     fn mul(self, rhs: Self) -> Self {
///         let nominator = self.nominator * rhs.nominator;
///         let denominator = self.denominator * rhs.denominator;
///         Rational::new(nominator, denominator)
///     }
/// }
///
/// // Euclid's two-thousand-year-old algorithm for finding the greatest common
/// // divisor.
/// fn gcd(x: usize, y: usize) -> usize {
///     let mut x = x;
///     let mut y = y;
///     while y != 0 {
///         let t = y;
///         y = x % y;
///         x = t;
///     }
///     x
/// }
///
/// assert_eq!(Rational::new(1, 2), Rational::new(2, 4));
/// assert_eq!(Rational::new(2, 3) * Rational::new(3, 4),
///            Rational::new(1, 2));
/// ```
///
/// Note that `RHS = Self` by default, but this is not mandatory. Here is an
/// implementation which enables multiplication of vectors by scalars, as is
/// done in linear algebra.
///
/// ```
/// use std::ops::Mul;
///
/// struct Scalar {value: usize};
///
/// #[derive(Debug)]
/// struct Vector {value: Vec<usize>};
///
/// impl Mul<Vector> for Scalar {
///     type Output = Vector;
///
///     fn mul(self, rhs: Vector) -> Vector {
///         Vector {value: rhs.value.iter().map(|v| self.value * v).collect()}
///     }
/// }
///
/// impl PartialEq<Vector> for Vector {
///     fn eq(&self, other: &Self) -> bool {
///         self.value == other.value
///     }
/// }
///
/// let scalar = Scalar{value: 3};
/// let vector = Vector{value: vec![2, 4, 6]};
/// assert_eq!(scalar * vector, Vector{value: vec![6, 12, 18]});
/// ```
#[lang = "mul"]
pub trait Mul<RHS=Self> {
    /// The resulting type after applying the `*` operator
    type Output;

    /// The method for the `*` operator
    fn mul(self, rhs: RHS) -> Self::Output;
}

macro_rules! mul_impl {
    ($($t:ty)*) => ($(
        impl Mul for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn mul(self, other: $t) -> $t { self * other }
        }
    )*)
}

mul_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `Div` trait is used to specify the functionality of `/`.
///
/// # Examples
///
/// Implementing a `Div`idable rational number struct:
///
/// ```
/// use std::ops::Div;
///
/// // The uniqueness of rational numbers in lowest terms is a consequence of
/// // the fundamental theorem of arithmetic.
/// #[derive(Eq)]
/// #[derive(PartialEq, Debug)]
/// struct Rational {
///     nominator: usize,
///     denominator: usize,
/// }
///
/// impl Rational {
///     fn new(nominator: usize, denominator: usize) -> Self {
///         if denominator == 0 {
///             panic!("Zero is an invalid denominator!");
///         }
///
///         // Reduce to lowest terms by dividing by the greatest common
///         // divisor.
///         let gcd = gcd(nominator, denominator);
///         Rational {
///             nominator: nominator / gcd,
///             denominator: denominator / gcd,
///         }
///     }
/// }
///
/// impl Div for Rational {
///     // The division of rational numbers is a closed operation.
///     type Output = Self;
///
///     fn div(self, rhs: Self) -> Self {
///         if rhs.nominator == 0 {
///             panic!("Cannot divide by zero-valued `Rational`!");
///         }
///
///         let nominator = self.nominator * rhs.denominator;
///         let denominator = self.denominator * rhs.nominator;
///         Rational::new(nominator, denominator)
///     }
/// }
///
/// // Euclid's two-thousand-year-old algorithm for finding the greatest common
/// // divisor.
/// fn gcd(x: usize, y: usize) -> usize {
///     let mut x = x;
///     let mut y = y;
///     while y != 0 {
///         let t = y;
///         y = x % y;
///         x = t;
///     }
///     x
/// }
///
/// fn main() {
///     assert_eq!(Rational::new(1, 2), Rational::new(2, 4));
///     assert_eq!(Rational::new(1, 2) / Rational::new(3, 4),
///                Rational::new(2, 3));
/// }
/// ```
///
/// Note that `RHS = Self` by default, but this is not mandatory. Here is an
/// implementation which enables division of vectors by scalars, as is done in
/// linear algebra.
///
/// ```
/// use std::ops::Div;
///
/// struct Scalar {value: f32};
///
/// #[derive(Debug)]
/// struct Vector {value: Vec<f32>};
///
/// impl Div<Scalar> for Vector {
///     type Output = Vector;
///
///     fn div(self, rhs: Scalar) -> Vector {
///         Vector {value: self.value.iter().map(|v| v / rhs.value).collect()}
///     }
/// }
///
/// impl PartialEq<Vector> for Vector {
///     fn eq(&self, other: &Self) -> bool {
///         self.value == other.value
///     }
/// }
///
/// let scalar = Scalar{value: 2f32};
/// let vector = Vector{value: vec![2f32, 4f32, 6f32]};
/// assert_eq!(vector / scalar, Vector{value: vec![1f32, 2f32, 3f32]});
/// ```
#[lang = "div"]
pub trait Div<RHS=Self> {
    /// The resulting type after applying the `/` operator
    type Output;

    /// The method for the `/` operator
    fn div(self, rhs: RHS) -> Self::Output;
}

macro_rules! div_impl_integer {
    ($($t:ty)*) => ($(
        /// This operation rounds towards zero, truncating any
        /// fractional part of the exact result.
        impl Div for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn div(self, other: $t) -> $t { self / other }
        }
    )*)
}

div_impl_integer! { usize u16 u32 u64 isize i16 i32 i64 }

macro_rules! div_impl_float {
    ($($t:ty)*) => ($(
        impl Div for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn div(self, other: $t) -> $t { self / other }
        }
    )*)
}

div_impl_float! { f32 f64 }

/// The `Neg` trait is used to specify the functionality of unary `-`.
///
/// # Examples
///
/// An implementation of `Neg` for `Sign`, which allows the use of `-` to
/// negate its value.
///
/// ```
/// use std::ops::Neg;
///
/// #[derive(Debug, PartialEq)]
/// enum Sign {
///     Negative,
///     Zero,
///     Positive,
/// }
///
/// impl Neg for Sign {
///     type Output = Sign;
///
///     fn neg(self) -> Sign {
///         match self {
///             Sign::Negative => Sign::Positive,
///             Sign::Zero => Sign::Zero,
///             Sign::Positive => Sign::Negative,
///         }
///     }
/// }
///
/// // a negative positive is a negative
/// assert_eq!(-Sign::Positive, Sign::Negative);
/// // a double negative is a positive
/// assert_eq!(-Sign::Negative, Sign::Positive);
/// // zero is its own negation
/// assert_eq!(-Sign::Zero, Sign::Zero);
/// ```
#[lang = "neg"]
pub trait Neg {
    /// The resulting type after applying the `-` operator
    type Output;

    /// The method for the unary `-` operator
    fn neg(self) -> Self::Output;
}

/// The `Not` trait is used to specify the functionality of unary `!`.
///
/// # Examples
///
/// An implementation of `Not` for `Answer`, which enables the use of `!` to
/// invert its value.
///
/// ```
/// use std::ops::Not;
///
/// #[derive(Debug, PartialEq)]
/// enum Answer {
///     Yes,
///     No,
/// }
///
/// impl Not for Answer {
///     type Output = Answer;
///
///     fn not(self) -> Answer {
///         match self {
///             Answer::Yes => Answer::No,
///             Answer::No => Answer::Yes
///         }
///     }
/// }
///
/// assert_eq!(!Answer::Yes, Answer::No);
/// assert_eq!(!Answer::No, Answer::Yes);
/// ```
#[lang = "not"]
pub trait Not {
    /// The resulting type after applying the `!` operator
    type Output;

    /// The method for the unary `!` operator
    fn not(self) -> Self::Output;
}

/// The `BitAnd` trait is used to specify the functionality of `&`.
///
/// # Examples
///
/// In this example, the `&` operator is lifted to a trivial `Scalar` type.
///
/// ```
/// use std::ops::BitAnd;
///
/// #[derive(Debug, PartialEq)]
/// struct Scalar(bool);
///
/// impl BitAnd for Scalar {
///     type Output = Self;
///
///     // rhs is the "right-hand side" of the expression `a & b`
///     fn bitand(self, rhs: Self) -> Self {
///         Scalar(self.0 & rhs.0)
///     }
/// }
///
/// fn main() {
///     assert_eq!(Scalar(true) & Scalar(true), Scalar(true));
///     assert_eq!(Scalar(true) & Scalar(false), Scalar(false));
///     assert_eq!(Scalar(false) & Scalar(true), Scalar(false));
///     assert_eq!(Scalar(false) & Scalar(false), Scalar(false));
/// }
/// ```
///
/// In this example, the `BitAnd` trait is implemented for a `BooleanVector`
/// struct.
///
/// ```
/// use std::ops::BitAnd;
///
/// #[derive(Debug, PartialEq)]
/// struct BooleanVector(Vec<bool>);
///
/// impl BitAnd for BooleanVector {
///     type Output = Self;
///
///     fn bitand(self, BooleanVector(rhs): Self) -> Self {
///         let BooleanVector(lhs) = self;
///         assert_eq!(lhs.len(), rhs.len());
///         BooleanVector(lhs.iter().zip(rhs.iter()).map(|(x, y)| *x && *y).collect())
///     }
/// }
///
/// fn main() {
///     let bv1 = BooleanVector(vec![true, true, false, false]);
///     let bv2 = BooleanVector(vec![true, false, true, false]);
///     let expected = BooleanVector(vec![true, false, false, false]);
///     assert_eq!(bv1 & bv2, expected);
/// }
/// ```
#[lang = "bitand"]
pub trait BitAnd<RHS=Self> {
    /// The resulting type after applying the `&` operator
    type Output;

    /// The method for the `&` operator
    fn bitand(self, rhs: RHS) -> Self::Output;
}

/// The `BitOr` trait is used to specify the functionality of `|`.
///
/// # Examples
///
/// In this example, the `|` operator is lifted to a trivial `Scalar` type.
///
/// ```
/// use std::ops::BitOr;
///
/// #[derive(Debug, PartialEq)]
/// struct Scalar(bool);
///
/// impl BitOr for Scalar {
///     type Output = Self;
///
///     // rhs is the "right-hand side" of the expression `a | b`
///     fn bitor(self, rhs: Self) -> Self {
///         Scalar(self.0 | rhs.0)
///     }
/// }
///
/// fn main() {
///     assert_eq!(Scalar(true) | Scalar(true), Scalar(true));
///     assert_eq!(Scalar(true) | Scalar(false), Scalar(true));
///     assert_eq!(Scalar(false) | Scalar(true), Scalar(true));
///     assert_eq!(Scalar(false) | Scalar(false), Scalar(false));
/// }
/// ```
///
/// In this example, the `BitOr` trait is implemented for a `BooleanVector`
/// struct.
///
/// ```
/// use std::ops::BitOr;
///
/// #[derive(Debug, PartialEq)]
/// struct BooleanVector(Vec<bool>);
///
/// impl BitOr for BooleanVector {
///     type Output = Self;
///
///     fn bitor(self, BooleanVector(rhs): Self) -> Self {
///         let BooleanVector(lhs) = self;
///         assert_eq!(lhs.len(), rhs.len());
///         BooleanVector(lhs.iter().zip(rhs.iter()).map(|(x, y)| *x || *y).collect())
///     }
/// }
///
/// fn main() {
///     let bv1 = BooleanVector(vec![true, true, false, false]);
///     let bv2 = BooleanVector(vec![true, false, true, false]);
///     let expected = BooleanVector(vec![true, true, true, false]);
///     assert_eq!(bv1 | bv2, expected);
/// }
/// ```
#[lang = "bitor"]
pub trait BitOr<RHS=Self> {
    /// The resulting type after applying the `|` operator
    type Output;

    /// The method for the `|` operator
    fn bitor(self, rhs: RHS) -> Self::Output;
}

/// The `AddAssign` trait is used to specify the functionality of `+=`.
///
/// # Examples
///
/// This example creates a `Point` struct that implements the `AddAssign`
/// trait, and then demonstrates add-assigning to a mutable `Point`.
///
/// ```
/// use std::ops::AddAssign;
///
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl AddAssign for Point {
///     fn add_assign(&mut self, other: Point) {
///         *self = Point {
///             x: self.x + other.x,
///             y: self.y + other.y,
///         };
///     }
/// }
///
/// impl PartialEq for Point {
///     fn eq(&self, other: &Self) -> bool {
///         self.x == other.x && self.y == other.y
///     }
/// }
///
/// let mut point = Point { x: 1, y: 0 };
/// point += Point { x: 2, y: 3 };
/// assert_eq!(point, Point { x: 3, y: 3 });
/// ```
#[lang = "add_assign"]
pub trait AddAssign<Rhs=Self> {
    /// The method for the `+=` operator
    fn add_assign(&mut self, Rhs);
}

macro_rules! add_assign_impl {
    ($($t:ty)+) => ($(
        impl AddAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn add_assign(&mut self, other: $t) { *self += other }
        }
    )+)
}

add_assign_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `SubAssign` trait is used to specify the functionality of `-=`.
///
/// # Examples
///
/// This example creates a `Point` struct that implements the `SubAssign`
/// trait, and then demonstrates sub-assigning to a mutable `Point`.
///
/// ```
/// use std::ops::SubAssign;
///
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl SubAssign for Point {
///     fn sub_assign(&mut self, other: Point) {
///         *self = Point {
///             x: self.x - other.x,
///             y: self.y - other.y,
///         };
///     }
/// }
///
/// impl PartialEq for Point {
///     fn eq(&self, other: &Self) -> bool {
///         self.x == other.x && self.y == other.y
///     }
/// }
///
/// let mut point = Point { x: 3, y: 3 };
/// point -= Point { x: 2, y: 3 };
/// assert_eq!(point, Point {x: 1, y: 0});
/// ```
#[lang = "sub_assign"]
pub trait SubAssign<Rhs=Self> {
    /// The method for the `-=` operator
    fn sub_assign(&mut self, Rhs);
}

macro_rules! sub_assign_impl {
    ($($t:ty)+) => ($(
        impl SubAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn sub_assign(&mut self, other: $t) { *self -= other }
        }
    )+)
}

sub_assign_impl! { usize u8 u16 u32 u64 isize i8 i16 i32 i64 f32 f64 }

#[lang = "mul_assign"]
pub trait MulAssign<Rhs=Self> {
    fn mul_assign(&mut self, Rhs);
}

impl MulAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn mul_assign(&mut self, other: isize) { *self *= other }
}

#[lang = "div_assign"]
pub trait DivAssign<Rhs=Self> {
    fn div_assign(&mut self, Rhs);
}

impl DivAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn div_assign(&mut self, other: isize) { *self /= other }
}

/// The `Deref` trait is used to specify the functionality of dereferencing
/// operations, like `*v`.
///
/// `Deref` also enables ['`Deref` coercions'][coercions].
///
/// [coercions]: ../../book/deref-coercions.html
///
/// # Examples
///
/// A struct with a single field which is accessible via dereferencing the
/// struct.
///
/// ```
/// use std::ops::Deref;
///
/// struct DerefExample<T> {
///     value: T
/// }
///
/// impl<T> Deref for DerefExample<T> {
///     type Target = T;
///
///     fn deref(&self) -> &T {
///         &self.value
///     }
/// }
///
/// fn main() {
///     let x = DerefExample { value: 'a' };
///     assert_eq!('a', *x);
/// }
/// ```
#[lang = "deref"]
pub trait Deref {
    /// The resulting type after dereferencing
    type Target: ?Sized;

    /// The method called to dereference a value
    fn deref(&self) -> &Self::Target;
}
