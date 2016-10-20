#![crate_name = "core"]
#![crate_type = "rlib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![feature(unboxed_closures)]
#![feature(allow_internal_unstable)]
#![feature(on_unimplemented)]
#![feature(prelude_import)]
#![feature(specialization)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

#[prelude_import]
use prelude::v1::*;

pub mod prelude;

pub mod clone;
pub mod cmp;
pub mod iter;
pub mod marker;
pub mod ops;
pub mod option;

#[lang = "eh_personality"] pub extern fn eh_personality() {}
