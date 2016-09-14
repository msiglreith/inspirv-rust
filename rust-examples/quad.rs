#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

mod std_spirv;
use std_spirv::*;

#[inspirv(interface)]
struct QuadVertex {
    #[inspirv(location = 0)]
    pos: Float4,

    #[inspirv(location = 1)]
    color: Float4,
}

#[inspirv(interface)]
struct QuadVarying {
    #[inspirv(location = 0)]
    #[inspirv(builtin = "Position")]
    pos: Float4,

    #[inspirv(location = 1)]
    color: Float4,
}

#[inspirv(interface)]
struct QuadFragment {
    #[inspirv(builtin = "FragCoord")]
    coord: Float4,
}

#[inspirv(interface)]
struct QuadOut {
    #[inspirv(location = 0)]
    color: Float4,
}

#[inspirv(const_buffer)]
struct Locals {

}

#[inspirv(entry_point = "vertex")]
fn vertex(input: QuadVertex) -> QuadVarying {
    QuadVarying {
        pos: input.pos,
        color: input.color,
    }
}

#[inspirv(entry_point = "fragment")]
fn fragment(input: QuadVarying, fragment: QuadFragment) -> QuadOut {
    let w = 800.0f32;
    let h = 600.0f32;
    QuadOut {
        color: Float4::new(fragment.coord.x / w, fragment.coord.y / h, 0.0f32, 1.0f32),
    }
}
