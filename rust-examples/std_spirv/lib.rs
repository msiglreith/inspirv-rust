
#![crate_name = "std_spirv"]
#![crate_type = "rlib"]

#![feature(no_core)]
#![feature(custom_attribute)]
#![feature(attr_literals)]

#![allow(unused_attributes)]

#![no_core]
extern crate core_spirv as core;

pub use core::clone;
pub use core::cmp;
pub use core::marker;
pub use core::ops;
pub use core::option;

pub mod interface;
pub mod matrix;
pub mod vector;

pub use self::interface::*;
pub use self::vector::*;
pub use self::matrix::*;
