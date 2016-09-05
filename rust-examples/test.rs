#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute)]
#![feature(optin_builtin_traits)]
#![feature(intrinsics)]
#![feature(attr_literals)]
#![allow(dead_code)]
#![no_core]

mod core;

#[inspirv(vector(base = "f32", components = 4))]
pub struct float4;

#[inspirv(interface(binding = 0))]
pub struct VertexPos {
    pos: float4,
}

#[inspirv(entry_point = "vertex")]
pub fn foo(input: VertexPos) {
    let y = float4;
    let mut x = 0u64;
    // x += pos as u64;
}
