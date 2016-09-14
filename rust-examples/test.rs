#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals)]
#![allow(dead_code)]
#![no_core]

mod std_spirv;
use std_spirv::*;

#[inspirv(interface)]
struct VertexInput {
    #[inspirv(location = 0)]
    pos: Float4,
}

#[inspirv(interface)]
struct VertexVarying {
    #[inspirv(location = 0)]
    #[inspirv(builtin = "Position")]
    pos: Float4,
}

#[inspirv(entry_point = "vertex")]
fn vertex()  {
    let a = Float4;
    let x = 0u32;
    let k = x as f32;
    let j = 0u32 as f32;

}
