// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functionality for ordering and comparison.
//!
//! This module defines both [`PartialOrd`] and [`PartialEq`] traits which are used
//! by the compiler to implement comparison operators. Rust programs may
//! implement [`PartialOrd`] to overload the `<`, `<=`, `>`, and `>=` operators,
//! and may implement [`PartialEq`] to overload the `==` and `!=` operators.
//!
//! [`PartialOrd`]: trait.PartialOrd.html
//! [`PartialEq`]: trait.PartialEq.html
//!
//! # Examples
//!
//! ```
//! let x: u32 = 0;
//! let y: u32 = 1;
//!
//! // these two lines are equivalent
//! assert_eq!(x < y, true);
//! assert_eq!(x.lt(&y), true);
//!
//! // these two lines are also equivalent
//! assert_eq!(x == y, false);
//! assert_eq!(x.eq(&y), false);
//! ```

use super::marker::Sized;

/// Trait for equality comparisons which are [partial equivalence
/// relations](http://en.wikipedia.org/wiki/Partial_equivalence_relation).
///
/// Formally, the equality must be (for all `a`, `b` and `c`):
///
/// - symmetric: `a == b` implies `b == a`; and
/// - transitive: `a == b` and `b == c` implies `a == c`.
///
/// Note that these requirements mean that the trait itself must be implemented
/// symmetrically and transitively: if `T: PartialEq<U>` and `U: PartialEq<V>`
/// then `U: PartialEq<T>` and `T: PartialEq<V>`.
///
/// ## How can I implement `PartialEq`?
///
/// PartialEq only requires the `eq` method to be implemented; `ne` is defined
/// in terms of it by default. Any manual implementation of `ne` *must* respect
/// the rule that `eq` is a strict inverse of `ne`; that is, `!(a == b)` if and
/// only if `a != b`.
///
/// # Examples
///
/// ```
/// let x: u32 = 0;
/// let y: u32 = 1;
///
/// assert_eq!(x == y, false);
/// assert_eq!(x.eq(&y), false);
/// ```
#[lang = "eq"]
pub trait PartialEq<Rhs: ?Sized = Self> {
    /// This method tests for `self` and `other` values to be equal, and is used
    /// by `==`.
    fn eq(&self, other: &Rhs) -> bool;

    /// This method tests for `!=`.
    #[inline]
    fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
}

pub trait Eq: PartialEq<Self> { }

#[lang = "ord"]
pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    /// This method tests less than (for `self` and `other`) and is used by the `<` operator.
    ///
    /// # Examples
    ///
    /// ```
    /// let result = 1.0 < 2.0;
    /// assert_eq!(result, true);
    ///
    /// let result = 2.0 < 1.0;
    /// assert_eq!(result, false);
    /// ```
    #[inline]
    fn lt(&self, other: &Rhs) -> bool;

    /// This method tests less than or equal to (for `self` and `other`) and is used by the `<=`
    /// operator.
    ///
    /// # Examples
    ///
    /// ```
    /// let result = 1.0 <= 2.0;
    /// assert_eq!(result, true);
    ///
    /// let result = 2.0 <= 2.0;
    /// assert_eq!(result, true);
    /// ```
    #[inline]
    fn le(&self, other: &Rhs) -> bool;

    /// This method tests greater than (for `self` and `other`) and is used by the `>` operator.
    ///
    /// # Examples
    ///
    /// ```
    /// let result = 1.0 > 2.0;
    /// assert_eq!(result, false);
    ///
    /// let result = 2.0 > 2.0;
    /// assert_eq!(result, false);
    /// ```
    #[inline]
    fn gt(&self, other: &Rhs) -> bool;

    /// This method tests greater than or equal to (for `self` and `other`) and is used by the `>=`
    /// operator.
    ///
    /// # Examples
    ///
    /// ```
    /// let result = 2.0 >= 1.0;
    /// assert_eq!(result, true);
    ///
    /// let result = 2.0 >= 2.0;
    /// assert_eq!(result, true);
    /// ```
    #[inline]
    fn ge(&self, other: &Rhs) -> bool;
}

pub trait Ord: Eq + PartialOrd<Self> {
}

macro_rules! partial_eq_impl {
    ($($t:ty)+) => ($(
        impl PartialEq for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn eq(&self, other: &$t) -> bool { *self == *other }
        }
    )+)
}

partial_eq_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

macro_rules! partial_ord_impl {
    ($($t:ty)+) => ($(
        impl PartialOrd for $t {
            #[inline]
            #[inspirv(compiler_builtin)]
            fn lt(&self, other: &$t) -> bool { *self < *other }

            #[inline]
            #[inspirv(compiler_builtin)]
            fn le(&self, other: &$t) -> bool { *self <= *other }

            #[inline]
            #[inspirv(compiler_builtin)]
            fn gt(&self, other: &$t) -> bool { *self > *other }

            #[inline]
            #[inspirv(compiler_builtin)]
            fn ge(&self, other: &$t) -> bool { *self >= *other }
        }
    )+)
}

partial_ord_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }