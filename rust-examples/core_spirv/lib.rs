// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # The Rust Core Library (inspirv)

#![crate_name = "core"]
#![crate_type = "rlib"]

#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![feature(unboxed_closures)]
#![feature(allow_internal_unstable)]
#![feature(on_unimplemented)]
#![feature(prelude_import)]
#![feature(specialization)]
#![feature(associated_type_defaults)]

#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

#[prelude_import]
use prelude::v1::*;

#[macro_use]
mod macros;

#[path = "num/f32.rs"]   pub mod f32;
#[path = "num/f64.rs"]   pub mod f64;

pub mod prelude;

pub mod clone;
pub mod cmp;
pub mod iter;
pub mod marker;
pub mod ops;
pub mod option;

#[lang = "eh_personality"] pub extern fn eh_personality() {}
