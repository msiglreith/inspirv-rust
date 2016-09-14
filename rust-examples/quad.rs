#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals)]
#![allow(dead_code)]
#![no_core]

mod core;


#[inspirv(vector(base = "f32", components = 2))]
struct float2 {
    x: f32,
    y: f32,
}
impl core::marker::Copy for float2 {}

#[inspirv(vector(base = "f32", components = 3))]
struct float3 {
    x: f32,
    y: f32,
    z: f32,
}
impl core::marker::Copy for float3 {}

#[inspirv(vector(base = "f32", components = 4))]
struct float4 {
    x: f32,
    y: f32,
    z: f32,
    w: f32,
}
impl core::marker::Copy for float4 {}

impl float4 {
    #[inspirv(intrinsic = "float4_new")]
    fn new(_x: f32, _y: f32, _z: f32, _w: f32) -> float4 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle2")]
    fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> float2 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle3")]
    fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> float3 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle4")]
    fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> float4 { loop {} }

    #[inspirv(intrinsic = "float4_shuffle4x2")]
    fn shuffle4x2(self, _v2: float2, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> float4 { loop {} }

    #[inspirv(intrinsic = "float4_shuffle4x3")]
    fn shuffle4x3(self, _v2: float3, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> float4 { loop {} }

    #[inspirv(intrinsic = "shuffle4_4x4")]
    fn shuffle4x4(self, _v2: float4, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> float4 { loop {} }
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
struct QuadFragment {
    #[inspirv(builtin = "FragCoord")]
    coord: float4,
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
fn fragment(input: QuadVarying, fragment: QuadFragment) -> QuadOut {
    let coord = fragment.coord;
    let w = 800.0f32;
    let h = 600.0f32;
    QuadOut {
        color: float4::new(fragment.coord.x / w, fragment.coord.y / h, 0.0f32, 1.0f32),
    }
}
