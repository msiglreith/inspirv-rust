#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

mod std_spirv;
use std_spirv::*;

pub enum Ordering {
    Less = 10,
    Equal = 2*1,
}

fn foo() {
    let mut x = Ordering::Less;
    let y = Ordering::Equal;
    let z = y;
}
