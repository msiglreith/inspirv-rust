#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals)]
#![allow(dead_code)]
#![no_core]

mod core;

#[inspirv(vector(base = "f32", components = 4))]
struct float4;
impl core::marker::Copy for float4 {}

impl float4 {
    #[inspirv(intrinsic = "float4_new")]
    pub fn new(x: f32, y: f32, z: f32, w: f32) -> float4 {
        float4::new(x, y, z, w)
    }
}


#[inspirv(interface)]
struct QuadVertex {
    #[inspirv(location = 0)]
    pos: float4,

    #[inspirv(location = 1)]
    color: float4,
}

#[inspirv(interface)]
struct QuadVarying {
    #[inspirv(location = 0)]
    #[inspirv(builtin = "Position")]
    pos: float4,

    #[inspirv(location = 1)]
    color: float4,
}

#[inspirv(interface)]
struct QuadOut {
    #[inspirv(location = 0)]
    color: float4,
}

#[inspirv(entry_point = "vertex")]
fn vertex(input: QuadVertex) -> QuadVarying {
    QuadVarying {
        pos: input.pos,
        color: input.color,
    }
}

#[inspirv(entry_point = "fragment")]
fn fragment(input: QuadVarying) -> QuadOut {
    QuadOut {
        color: float4::new(0.0f32, 1.0f32, 1.0f32, 1.0f32),
    }
}
