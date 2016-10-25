// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The first version of the prelude of The Rust Standard Library.

// Reexported core operators
#[doc(no_inline)] pub use marker::{Copy, Sized, Sync};
#[doc(no_inline)] pub use ops::{Fn, FnMut, FnOnce};

// Reexported types and traits
#[doc(no_inline)] pub use clone::Clone;
#[doc(no_inline)] pub use cmp::{PartialEq, PartialOrd, Eq, Ord};
// #[doc(no_inline)] pub use default::Default;
// #[doc(no_inline)] pub use iter::{Iterator, IntoIterator};
#[doc(no_inline)] pub use option::Option::{self, Some, None};
#[doc(no_inline)] pub use interface::{Attributes, Cbuffer};
#[doc(no_inline)] pub use matrix::{Matrix2x2, Matrix3x3, Matrix4x4};
#[doc(no_inline)] pub use vector::{Vector2, Vector3, Vector4, Float2, Float3, Float4};
