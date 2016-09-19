#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

mod std_spirv;
use std_spirv::*;

fn foo() {
    let mut x = 0;
    let y = &mut x;
    *y = 2;
}