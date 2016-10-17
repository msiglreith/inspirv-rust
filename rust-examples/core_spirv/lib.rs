#![crate_name = "core_spirv"]
#![crate_type = "rlib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![feature(unboxed_closures)]
#![feature(allow_internal_unstable)]
#![feature(on_unimplemented)]
#![feature(specialization)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

pub mod clone;
pub mod cmp;
pub mod iter;
pub mod marker;
pub mod ops;
pub mod option;
