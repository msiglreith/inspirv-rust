// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Overloadable operators.
//!
//! Implementing these traits allows you to overload certain operators.
//!
//! Some of these traits are imported by the prelude, so they are available in
//! every Rust program. Only operators backed by traits can be overloaded. For
//! example, the addition operator (`+`) can be overloaded through the [`Add`]
//! trait, but since the assignment operator (`=`) has no backing trait, there
//! is no way of overloading its semantics. Additionally, this module does not
//! provide any mechanism to create new operators. If traitless overloading or
//! custom operators are required, you should look toward macros or compiler
//! plugins to extend Rust's syntax.
//!
//! Note that the `&&` and `||` operators short-circuit, i.e. they only
//! evaluate their second operand if it contributes to the result. Since this
//! behavior is not enforceable by traits, `&&` and `||` are not supported as
//! overloadable operators.
//!
//! Many of the operators take their operands by value. In non-generic
//! contexts involving built-in types, this is usually not a problem.
//! However, using these operators in generic code, requires some
//! attention if values have to be reused as opposed to letting the operators
//! consume them. One option is to occasionally use [`clone()`].
//! Another option is to rely on the types involved providing additional
//! operator implementations for references. For example, for a user-defined
//! type `T` which is supposed to support addition, it is probably a good
//! idea to have both `T` and `&T` implement the traits [`Add<T>`][`Add`] and
//! [`Add<&T>`][`Add`] so that generic code can be written without unnecessary
//! cloning.

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

/// The `Rem` trait is used to specify the functionality of `%`.
///
/// # Examples
///
/// This example implements `Rem` on a `SplitSlice` object. After `Rem` is
/// implemented, one can use the `%` operator to find out what the remaining
/// elements of the slice would be after splitting it into equal slices of a
/// given length.
///
/// ```
/// use std::ops::Rem;
///
/// #[derive(PartialEq, Debug)]
/// struct SplitSlice<'a, T: 'a> {
///     slice: &'a [T],
/// }
///
/// impl<'a, T> Rem<usize> for SplitSlice<'a, T> {
///     type Output = SplitSlice<'a, T>;
///
///     fn rem(self, modulus: usize) -> Self {
///         let len = self.slice.len();
///         let rem = len % modulus;
///         let start = len - rem;
///         SplitSlice {slice: &self.slice[start..]}
///     }
/// }
///
/// // If we were to divide &[0, 1, 2, 3, 4, 5, 6, 7] into slices of size 3,
/// // the remainder would be &[6, 7]
/// assert_eq!(SplitSlice { slice: &[0, 1, 2, 3, 4, 5, 6, 7] } % 3,
///            SplitSlice { slice: &[6, 7] });
/// ```
#[lang = "rem"]
pub trait Rem<RHS=Self> {
    /// The resulting type after applying the `%` operator    
    type Output = Self;

    /// The method for the `%` operator    
    fn rem(self, rhs: RHS) -> Self::Output;
}


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

macro_rules! neg_impl_core {
    ($id:ident => $body:expr, $($t:ty)*) => ($(
        impl Neg for $t {
            type Output = $t;

            #[inline]
            #[inspirv(compiler_builtin)]
            fn neg(self) -> $t { let $id = self; $body }
        }

        forward_ref_unop! { impl Neg, neg for $t }
    )*)
}

macro_rules! neg_impl_numeric {
    ($($t:ty)*) => { neg_impl_core!{ x => -x, $($t)*} }
}

neg_impl_numeric! { isize i16 i32 i64 f32 f64 }

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
#[lang = "bitor"]
pub trait BitOr<RHS=Self> {
    /// The resulting type after applying the `|` operator
    type Output;

    /// The method for the `|` operator
    fn bitor(self, rhs: RHS) -> Self::Output;
}


/// The `BitXor` trait is used to specify the functionality of `^`.
///
/// # Examples
///
/// In this example, the `^` operator is lifted to a trivial `Scalar` type.
///
/// ```
/// use std::ops::BitXor;
///
/// #[derive(Debug, PartialEq)]
/// struct Scalar(bool);
///
/// impl BitXor for Scalar {
///     type Output = Self;
///
///     // rhs is the "right-hand side" of the expression `a ^ b`
///     fn bitxor(self, rhs: Self) -> Self {
///         Scalar(self.0 ^ rhs.0)
///     }
/// }
///
/// fn main() {
///     assert_eq!(Scalar(true) ^ Scalar(true), Scalar(false));
///     assert_eq!(Scalar(true) ^ Scalar(false), Scalar(true));
///     assert_eq!(Scalar(false) ^ Scalar(true), Scalar(true));
///     assert_eq!(Scalar(false) ^ Scalar(false), Scalar(false));
/// }
/// ```
#[lang = "bitxor"]
pub trait BitXor<RHS=Self> {
    /// The resulting type after applying the `^` operator    
    type Output;

    /// The method for the `^` operator    
    fn bitxor(self, rhs: RHS) -> Self::Output;
}


/// The `Shl` trait is used to specify the functionality of `<<`.
///
/// # Examples
///
/// An implementation of `Shl` that lifts the `<<` operation on integers to a
/// `Scalar` struct.
///
/// ```
/// use std::ops::Shl;
///
/// #[derive(PartialEq, Debug)]
/// struct Scalar(usize);
///
/// impl Shl<Scalar> for Scalar {
///     type Output = Self;
///
///     fn shl(self, Scalar(rhs): Self) -> Scalar {
///         let Scalar(lhs) = self;
///         Scalar(lhs << rhs)
///     }
/// }
/// fn main() {
///     assert_eq!(Scalar(4) << Scalar(2), Scalar(16));
/// }
/// ```
#[lang = "shl"]
pub trait Shl<RHS> {
    /// The resulting type after applying the `<<` operator    
    type Output;

    /// The method for the `<<` operator    
    fn shl(self, rhs: RHS) -> Self::Output;
}

/// The `Shr` trait is used to specify the functionality of `>>`.
///
/// # Examples
///
/// An implementation of `Shr` that lifts the `>>` operation on integers to a
/// `Scalar` struct.
///
/// ```
/// use std::ops::Shr;
///
/// #[derive(PartialEq, Debug)]
/// struct Scalar(usize);
///
/// impl Shr<Scalar> for Scalar {
///     type Output = Self;
///
///     fn shr(self, Scalar(rhs): Self) -> Scalar {
///         let Scalar(lhs) = self;
///         Scalar(lhs >> rhs)
///     }
/// }
/// fn main() {
///     assert_eq!(Scalar(16) >> Scalar(2), Scalar(4));
/// }
/// ```
///
/// An implementation of `Shr` that spins a vector rightward by a given amount.
///
/// ```
/// use std::ops::Shr;
///
/// #[derive(PartialEq, Debug)]
/// struct SpinVector<T: Clone> {
///     vec: Vec<T>,
/// }
#[lang = "shr"]
pub trait Shr<RHS> {
    /// The resulting type after applying the `>>` operator    
    type Output;

    /// The method for the `>>` operator    
    fn shr(self, rhs: RHS) -> Self::Output;
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

sub_assign_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `MulAssign` trait is used to specify the functionality of `*=`.
///
/// # Examples
///
/// A trivial implementation of `MulAssign`. When `Foo *= Foo` happens, it ends up
/// calling `mul_assign`, and therefore, `main` prints `Multiplying!`.
///
/// ```
/// use std::ops::MulAssign;
///
/// struct Foo;
///
/// impl MulAssign for Foo {
///     fn mul_assign(&mut self, _rhs: Foo) {
///         println!("Multiplying!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo *= Foo;
/// }
/// ```
#[lang = "mul_assign"]
pub trait MulAssign<Rhs=Self> {
    fn mul_assign(&mut self, Rhs);
}

macro_rules! mul_assign_impl {
    ($($t:ty)+) => ($(
        impl MulAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn mul_assign(&mut self, other: $t) { *self *= other }
        }
    )+)
}

mul_assign_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `DivAssign` trait is used to specify the functionality of `/=`.
///
/// # Examples
///
/// A trivial implementation of `DivAssign`. When `Foo /= Foo` happens, it ends up
/// calling `div_assign`, and therefore, `main` prints `Dividing!`.
///
/// ```
/// use std::ops::DivAssign;
///
/// struct Foo;
///
/// impl DivAssign for Foo {
///     fn div_assign(&mut self, _rhs: Foo) {
///         println!("Dividing!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo /= Foo;
/// }
/// ```
#[lang = "div_assign"]
pub trait DivAssign<Rhs=Self> {
    fn div_assign(&mut self, Rhs);
}

macro_rules! div_assign_impl {
    ($($t:ty)+) => ($(
        impl DivAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn div_assign(&mut self, other: $t) { *self /= other }
        }
    )+)
}

div_assign_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `RemAssign` trait is used to specify the functionality of `%=`.
///
/// # Examples
///
/// A trivial implementation of `RemAssign`. When `Foo %= Foo` happens, it ends up
/// calling `rem_assign`, and therefore, `main` prints `Remainder-ing!`.
///
/// ```
/// use std::ops::RemAssign;
///
/// struct Foo;
///
/// impl RemAssign for Foo {
///     fn rem_assign(&mut self, _rhs: Foo) {
///         println!("Remainder-ing!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo %= Foo;
/// }
/// ```
#[lang = "rem_assign"]
pub trait RemAssign<Rhs=Self> {
    /// The method for the `%=` operator    
    fn rem_assign(&mut self, Rhs);
}

macro_rules! rem_assign_impl {
    ($($t:ty)+) => ($(
        impl RemAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn rem_assign(&mut self, other: $t) { *self %= other }
        }
    )+)
}

rem_assign_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

/// The `BitAndAssign` trait is used to specify the functionality of `&=`.
///
/// # Examples
///
/// In this example, the `&=` operator is lifted to a trivial `Scalar` type.
///
/// ```
/// use std::ops::BitAndAssign;
///
/// #[derive(Debug, PartialEq)]
/// struct Scalar(bool);
///
/// impl BitAndAssign for Scalar {
///     // rhs is the "right-hand side" of the expression `a &= b`
///     fn bitand_assign(&mut self, rhs: Self) {
///         *self = Scalar(self.0 & rhs.0)
///     }
/// }
///
/// fn main() {
///     let mut scalar = Scalar(true);
///     scalar &= Scalar(true);
///     assert_eq!(scalar, Scalar(true));
///
///     let mut scalar = Scalar(true);
///     scalar &= Scalar(false);
///     assert_eq!(scalar, Scalar(false));
///
///     let mut scalar = Scalar(false);
///     scalar &= Scalar(true);
///     assert_eq!(scalar, Scalar(false));
///
///     let mut scalar = Scalar(false);
///     scalar &= Scalar(false);
///     assert_eq!(scalar, Scalar(false));
/// }
/// ```
#[lang = "bitand_assign"]
pub trait BitAndAssign<Rhs=Self> {
    /// The method for the `&=` operator    
    fn bitand_assign(&mut self, Rhs);
}

macro_rules! bitand_assign_impl {
    ($($t:ty)+) => ($(
        impl BitAndAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn bitand_assign(&mut self, other: $t) { *self &= other }
        }
    )+)
}

bitand_assign_impl! { bool usize u16 u32 u64 isize i16 i32 i64 }

/// The `BitOrAssign` trait is used to specify the functionality of `|=`.
///
/// # Examples
///
/// A trivial implementation of `BitOrAssign`. When `Foo |= Foo` happens, it ends up
/// calling `bitor_assign`, and therefore, `main` prints `Bitwise Or-ing!`.
///
/// ```
/// use std::ops::BitOrAssign;
///
/// struct Foo;
///
/// impl BitOrAssign for Foo {
///     fn bitor_assign(&mut self, _rhs: Foo) {
///         println!("Bitwise Or-ing!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo |= Foo;
/// }
/// ```
#[lang = "bitor_assign"]
pub trait BitOrAssign<Rhs=Self> {
    /// The method for the `|=` operator    
    fn bitor_assign(&mut self, Rhs);
}

macro_rules! bitor_assign_impl {
    ($($t:ty)+) => ($(
        impl BitOrAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn bitor_assign(&mut self, other: $t) { *self |= other }
        }
    )+)
}

bitor_assign_impl! { bool usize u16 u32 u64 isize i16 i32 i64 }

/// The `BitXorAssign` trait is used to specify the functionality of `^=`.
///
/// # Examples
///
/// A trivial implementation of `BitXorAssign`. When `Foo ^= Foo` happens, it ends up
/// calling `bitxor_assign`, and therefore, `main` prints `Bitwise Xor-ing!`.
///
/// ```
/// use std::ops::BitXorAssign;
///
/// struct Foo;
///
/// impl BitXorAssign for Foo {
///     fn bitxor_assign(&mut self, _rhs: Foo) {
///         println!("Bitwise Xor-ing!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo ^= Foo;
/// }
/// ```
#[lang = "bitxor_assign"]
pub trait BitXorAssign<Rhs=Self> {
    /// The method for the `^=` operator    
    fn bitxor_assign(&mut self, Rhs);
}

macro_rules! bitxor_assign_impl {
    ($($t:ty)+) => ($(
        impl BitXorAssign for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn bitxor_assign(&mut self, other: $t) { *self ^= other }
        }
    )+)
}

bitxor_assign_impl! { bool usize u16 u32 u64 isize i16 i32 i64 }

/// The `ShlAssign` trait is used to specify the functionality of `<<=`.
///
/// # Examples
///
/// A trivial implementation of `ShlAssign`. When `Foo <<= Foo` happens, it ends up
/// calling `shl_assign`, and therefore, `main` prints `Shifting left!`.
///
/// ```
/// use std::ops::ShlAssign;
///
/// struct Foo;
///
/// impl ShlAssign<Foo> for Foo {
///     fn shl_assign(&mut self, _rhs: Foo) {
///         println!("Shifting left!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo <<= Foo;
/// }
/// ```
#[lang = "shl_assign"]
pub trait ShlAssign<Rhs> {
    /// The method for the `<<=` operator    
    fn shl_assign(&mut self, Rhs);
}

macro_rules! shl_assign_impl {
    ($t:ty, $f:ty) => (
        impl ShlAssign<$f> for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn shl_assign(&mut self, other: $f) {
                *self <<= other
            }
        }
    )
}

macro_rules! shl_assign_impl_all {
    ($($t:ty)*) => ($(
        shl_assign_impl! { $t, u16 }
        shl_assign_impl! { $t, u32 }
        shl_assign_impl! { $t, u64 }
        shl_assign_impl! { $t, usize }

        shl_assign_impl! { $t, i16 }
        shl_assign_impl! { $t, i32 }
        shl_assign_impl! { $t, i64 }
        shl_assign_impl! { $t, isize }
    )*)
}

shl_assign_impl_all! { u16 u32 u64 usize i16 i32 i64 isize }

/// The `ShrAssign` trait is used to specify the functionality of `>>=`.
///
/// # Examples
///
/// A trivial implementation of `ShrAssign`. When `Foo >>= Foo` happens, it ends up
/// calling `shr_assign`, and therefore, `main` prints `Shifting right!`.
///
/// ```
/// use std::ops::ShrAssign;
///
/// struct Foo;
///
/// impl ShrAssign<Foo> for Foo {
///     fn shr_assign(&mut self, _rhs: Foo) {
///         println!("Shifting right!");
///     }
/// }
///
/// # #[allow(unused_assignments)]
/// fn main() {
///     let mut foo = Foo;
///     foo >>= Foo;
/// }
/// ```
#[lang = "shr_assign"]
pub trait ShrAssign<Rhs=Self> {
    /// The method for the `>>=` operator    
    fn shr_assign(&mut self, Rhs);
}

macro_rules! shr_assign_impl {
    ($t:ty, $f:ty) => (
        impl ShrAssign<$f> for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn shr_assign(&mut self, other: $f) {
                *self >>= other
            }
        }
    )
}

macro_rules! shr_assign_impl_all {
    ($($t:ty)*) => ($(
        shr_assign_impl! { $t, u16 }
        shr_assign_impl! { $t, u32 }
        shr_assign_impl! { $t, u64 }
        shr_assign_impl! { $t, usize }

        shr_assign_impl! { $t, i16 }
        shr_assign_impl! { $t, i32 }
        shr_assign_impl! { $t, i64 }
        shr_assign_impl! { $t, isize }
    )*)
}

shr_assign_impl_all! { u16 u32 u64 usize i16 i32 i64 isize }

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

/// An unbounded range. Use `..` (two dots) for its shorthand.
///
/// Its primary use case is slicing index. It cannot serve as an iterator
/// because it doesn't have a starting point.
///
/// # Examples
///
/// The `..` syntax is a `RangeFull`:
///
/// ```
/// assert_eq!((..), std::ops::RangeFull);
/// ```
///
/// It does not have an `IntoIterator` implementation, so you can't use it in a
/// `for` loop directly. This won't compile:
///
/// ```ignore
/// for i in .. {
///    // ...
/// }
/// ```
///
/// Used as a slicing index, `RangeFull` produces the full array as a slice.
///
/// ```
/// let arr = [0, 1, 2, 3];
/// assert_eq!(arr[ .. ], [0,1,2,3]);  // RangeFull
/// assert_eq!(arr[ ..3], [0,1,2  ]);
/// assert_eq!(arr[1.. ], [  1,2,3]);
/// assert_eq!(arr[1..3], [  1,2  ]);
/// ```
pub struct RangeFull;

/// A (half-open) range which is bounded at both ends: { x | start <= x < end }.
/// Use `start..end` (two dots) for its shorthand.
///
/// See the [`contains()`](#method.contains) method for its characterization.
///
/// # Examples
///
/// ```
/// fn main() {
///     assert_eq!((3..5), std::ops::Range{ start: 3, end: 5 });
///     assert_eq!(3+4+5, (3..6).sum());
///
///     let arr = [0, 1, 2, 3];
///     assert_eq!(arr[ .. ], [0,1,2,3]);
///     assert_eq!(arr[ ..3], [0,1,2  ]);
///     assert_eq!(arr[1.. ], [  1,2,3]);
///     assert_eq!(arr[1..3], [  1,2  ]);  // Range
/// }
/// ```
pub struct Range<Idx> {
    /// The lower bound of the range (inclusive).
    pub start: Idx,
    /// The upper bound of the range (exclusive).
    pub end: Idx,
}

/// A range which is only bounded below: { x | start <= x }.
/// Use `start..` for its shorthand.
///
/// See the [`contains()`](#method.contains) method for its characterization.
///
/// Note: Currently, no overflow checking is done for the iterator
/// implementation; if you use an integer range and the integer overflows, it
/// might panic in debug mode or create an endless loop in release mode. This
/// overflow behavior might change in the future.
///
/// # Examples
///
/// ```
/// fn main() {
///     assert_eq!((2..), std::ops::RangeFrom{ start: 2 });
///     assert_eq!(2+3+4, (2..).take(3).sum());
///
///     let arr = [0, 1, 2, 3];
///     assert_eq!(arr[ .. ], [0,1,2,3]);
///     assert_eq!(arr[ ..3], [0,1,2  ]);
///     assert_eq!(arr[1.. ], [  1,2,3]);  // RangeFrom
///     assert_eq!(arr[1..3], [  1,2  ]);
/// }
/// ```
pub struct RangeFrom<Idx> {
    /// The lower bound of the range (inclusive).
    pub start: Idx,
}

/// A range which is only bounded above: { x | x < end }.
/// Use `..end` (two dots) for its shorthand.
///
/// See the [`contains()`](#method.contains) method for its characterization.
///
/// It cannot serve as an iterator because it doesn't have a starting point.
///
/// # Examples
///
/// The `..{integer}` syntax is a `RangeTo`:
///
/// ```
/// assert_eq!((..5), std::ops::RangeTo{ end: 5 });
/// ```
///
/// It does not have an `IntoIterator` implementation, so you can't use it in a
/// `for` loop directly. This won't compile:
///
/// ```ignore
/// for i in ..5 {
///     // ...
/// }
/// ```
///
/// When used as a slicing index, `RangeTo` produces a slice of all array
/// elements before the index indicated by `end`.
///
/// ```
/// let arr = [0, 1, 2, 3];
/// assert_eq!(arr[ .. ], [0,1,2,3]);
/// assert_eq!(arr[ ..3], [0,1,2  ]);  // RangeTo
/// assert_eq!(arr[1.. ], [  1,2,3]);
/// assert_eq!(arr[1..3], [  1,2  ]);
/// ```
pub struct RangeTo<Idx> {
    /// The upper bound of the range (exclusive).
    pub end: Idx,
}

/// A version of the call operator that takes an immutable receiver.
///
/// # Examples
///
/// Closures automatically implement this trait, which allows them to be
/// invoked. Note, however, that `Fn` takes an immutable reference to any
/// captured variables. To take a mutable capture, implement [`FnMut`], and to
/// consume the capture, implement [`FnOnce`].
///
/// [`FnMut`]: trait.FnMut.html
/// [`FnOnce`]: trait.FnOnce.html
///
/// ```
/// let square = |x| x * x;
/// assert_eq!(square(5), 25);
/// ```
///
/// Closures can also be passed to higher-level functions through a `Fn`
/// parameter (or a `FnMut` or `FnOnce` parameter, which are supertraits of
/// `Fn`).
///
/// ```
/// fn call_with_one<F>(func: F) -> usize
///     where F: Fn(usize) -> usize {
///     func(1)
/// }
///
/// let double = |x| x * 2;
/// assert_eq!(call_with_one(double), 2);
/// ```
#[lang = "fn"]
#[rustc_paren_sugar]
#[fundamental]
pub trait Fn<Args> : FnMut<Args> {
    /// This is called when the call operator is used.
    extern "rust-call" fn call(&self, args: Args) -> Self::Output;
}

/// A version of the call operator that takes a mutable receiver.
///
/// # Examples
///
/// Closures that mutably capture variables automatically implement this trait,
/// which allows them to be invoked.
///
/// ```
/// let mut x = 5;
/// {
///     let mut square_x = || x *= x;
///     square_x();
/// }
/// assert_eq!(x, 25);
/// ```
///
/// Closures can also be passed to higher-level functions through a `FnMut`
/// parameter (or a `FnOnce` parameter, which is a supertrait of `FnMut`).
///
/// ```
/// fn do_twice<F>(mut func: F)
///     where F: FnMut()
/// {
///     func();
///     func();
/// }
///
/// let mut x: usize = 1;
/// {
///     let add_two_to_x = || x += 2;
///     do_twice(add_two_to_x);
/// }
///
/// assert_eq!(x, 5);
/// ```
#[lang = "fn_mut"]
#[rustc_paren_sugar]
#[fundamental]
pub trait FnMut<Args> : FnOnce<Args> {
    /// This is called when the call operator is used.
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output;
}

/// A version of the call operator that takes a by-value receiver.
///
/// # Examples
///
/// By-value closures automatically implement this trait, which allows them to
/// be invoked.
///
/// ```
/// let x = 5;
/// let square_x = move || x * x;
/// assert_eq!(square_x(), 25);
/// ```
///
/// By-value Closures can also be passed to higher-level functions through a
/// `FnOnce` parameter.
///
/// ```
/// fn consume_with_relish<F>(func: F)
///     where F: FnOnce() -> String
/// {
///     // `func` consumes its captured variables, so it cannot be run more
///     // than once
///     println!("Consumed: {}", func());
///
///     println!("Delicious!");
///
///     // Attempting to invoke `func()` again will throw a `use of moved
///     // value` error for `func`
/// }
///
/// let x = String::from("x");
/// let consume_and_return_x = move || x;
/// consume_with_relish(consume_and_return_x);
///
/// // `consume_and_return_x` can no longer be invoked at this point
/// ```
#[lang = "fn_once"]
#[rustc_paren_sugar]
#[fundamental]
pub trait FnOnce<Args> {
    /// The returned type after the call operator is used.
    type Output;

    /// This is called when the call operator is used.
    extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
}
