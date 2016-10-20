// Copyright 2013-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use marker::Sized;
use iter::Iterator;

/// Conversion from an `Iterator`.
///
/// By implementing `FromIterator` for a type, you define how it will be
/// created from an iterator. This is common for types which describe a
/// collection of some kind.
///
/// `FromIterator`'s [`from_iter()`] is rarely called explicitly, and is instead
/// used through [`Iterator`]'s [`collect()`] method. See [`collect()`]'s
/// documentation for more examples.
///
/// [`from_iter()`]: #tymethod.from_iter
/// [`Iterator`]: trait.Iterator.html
/// [`collect()`]: trait.Iterator.html#method.collect
///
/// See also: [`IntoIterator`].
///
/// [`IntoIterator`]: trait.IntoIterator.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::iter::FromIterator;
///
/// let five_fives = std::iter::repeat(5).take(5);
///
/// let v = Vec::from_iter(five_fives);
///
/// assert_eq!(v, vec![5, 5, 5, 5, 5]);
/// ```
///
/// Using [`collect()`] to implicitly use `FromIterator`:
///
/// ```
/// let five_fives = std::iter::repeat(5).take(5);
///
/// let v: Vec<i32> = five_fives.collect();
///
/// assert_eq!(v, vec![5, 5, 5, 5, 5]);
/// ```
///
/// Implementing `FromIterator` for your type:
///
/// ```
/// use std::iter::FromIterator;
///
/// // A sample collection, that's just a wrapper over Vec<T>
/// #[derive(Debug)]
/// struct MyCollection(Vec<i32>);
///
/// // Let's give it some methods so we can create one and add things
/// // to it.
/// impl MyCollection {
///     fn new() -> MyCollection {
///         MyCollection(Vec::new())
///     }
///
///     fn add(&mut self, elem: i32) {
///         self.0.push(elem);
///     }
/// }
///
/// // and we'll implement FromIterator
/// impl FromIterator<i32> for MyCollection {
///     fn from_iter<I: IntoIterator<Item=i32>>(iter: I) -> Self {
///         let mut c = MyCollection::new();
///
///         for i in iter {
///             c.add(i);
///         }
///
///         c
///     }
/// }
///
/// // Now we can make a new iterator...
/// let iter = (0..5).into_iter();
///
/// // ... and make a MyCollection out of it
/// let c = MyCollection::from_iter(iter);
///
/// assert_eq!(c.0, vec![0, 1, 2, 3, 4]);
///
/// // collect works too!
///
/// let iter = (0..5).into_iter();
/// let c: MyCollection = iter.collect();
///
/// assert_eq!(c.0, vec![0, 1, 2, 3, 4]);
/// ```
#[rustc_on_unimplemented="a collection of type `{Self}` cannot be \
                          built from an iterator over elements of type `{A}`"]
pub trait FromIterator<A>: Sized {
    /// Creates a value from an iterator.
    ///
    /// See the [module-level documentation] for more.
    ///
    /// [module-level documentation]: trait.FromIterator.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::iter::FromIterator;
    ///
    /// let five_fives = std::iter::repeat(5).take(5);
    ///
    /// let v = Vec::from_iter(five_fives);
    ///
    /// assert_eq!(v, vec![5, 5, 5, 5, 5]);
    /// ```    
    fn from_iter<T: IntoIterator<Item=A>>(iter: T) -> Self;
}

/// Conversion into an `Iterator`.
///
/// By implementing `IntoIterator` for a type, you define how it will be
/// converted to an iterator. This is common for types which describe a
/// collection of some kind.
///
/// One benefit of implementing `IntoIterator` is that your type will [work
/// with Rust's `for` loop syntax](index.html#for-loops-and-intoiterator).
///
/// See also: [`FromIterator`].
///
/// [`FromIterator`]: trait.FromIterator.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// let v = vec![1, 2, 3];
///
/// let mut iter = v.into_iter();
///
/// let n = iter.next();
/// assert_eq!(Some(1), n);
///
/// let n = iter.next();
/// assert_eq!(Some(2), n);
///
/// let n = iter.next();
/// assert_eq!(Some(3), n);
///
/// let n = iter.next();
/// assert_eq!(None, n);
/// ```
///
/// Implementing `IntoIterator` for your type:
///
/// ```
/// // A sample collection, that's just a wrapper over Vec<T>
/// #[derive(Debug)]
/// struct MyCollection(Vec<i32>);
///
/// // Let's give it some methods so we can create one and add things
/// // to it.
/// impl MyCollection {
///     fn new() -> MyCollection {
///         MyCollection(Vec::new())
///     }
///
///     fn add(&mut self, elem: i32) {
///         self.0.push(elem);
///     }
/// }
///
/// // and we'll implement IntoIterator
/// impl IntoIterator for MyCollection {
///     type Item = i32;
///     type IntoIter = ::std::vec::IntoIter<i32>;
///
///     fn into_iter(self) -> Self::IntoIter {
///         self.0.into_iter()
///     }
/// }
///
/// // Now we can make a new collection...
/// let mut c = MyCollection::new();
///
/// // ... add some stuff to it ...
/// c.add(0);
/// c.add(1);
/// c.add(2);
///
/// // ... and then turn it into an Iterator:
/// for (i, n) in c.into_iter().enumerate() {
///     assert_eq!(i as i32, n);
/// }
/// ```
pub trait IntoIterator {
    /// The type of the elements being iterated over.    
    type Item;

    /// Which kind of iterator are we turning this into?    
    type IntoIter: Iterator<Item=Self::Item>;

    /// Creates an iterator from a value.
    ///
    /// See the [module-level documentation] for more.
    ///
    /// [module-level documentation]: trait.IntoIterator.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let v = vec![1, 2, 3];
    ///
    /// let mut iter = v.into_iter();
    ///
    /// let n = iter.next();
    /// assert_eq!(Some(1), n);
    ///
    /// let n = iter.next();
    /// assert_eq!(Some(2), n);
    ///
    /// let n = iter.next();
    /// assert_eq!(Some(3), n);
    ///
    /// let n = iter.next();
    /// assert_eq!(None, n);
    /// ```    
    fn into_iter(self) -> Self::IntoIter;
}

impl<I: Iterator> IntoIterator for I {
    type Item = I::Item;
    type IntoIter = I;

    fn into_iter(self) -> I {
        self
    }
}