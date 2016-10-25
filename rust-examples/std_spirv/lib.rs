
#![crate_name = "std"]
#![crate_type = "rlib"]

#![feature(custom_attribute)]
#![feature(attr_literals)]
#![feature(prelude_import)]

#![allow(unused_attributes)]

#![no_std]
extern crate core as __core;

#[prelude_import]
#[allow(unused)]
use prelude::v1::*;

pub mod prelude;

pub use core::clone;
pub use core::cmp;
pub use core::marker;
pub use core::ops;
pub use core::option;

pub use core::f32;
pub use core::f64;

pub mod interface;
pub mod matrix;
pub mod vector;

pub use self::interface::*;
pub use self::vector::*;
pub use self::matrix::*;
