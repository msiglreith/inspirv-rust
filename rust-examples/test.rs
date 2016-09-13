#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals)]
#![allow(dead_code)]
#![no_core]

mod core;

#[inspirv(vector(base = "f32", components = 2))]
struct float2;
impl core::marker::Copy for float2 {}

#[inspirv(vector(base = "f32", components = 3))]
struct float3;
impl core::marker::Copy for float3 {}

#[inspirv(vector(base = "f32", components = 4))]
struct float4;
impl core::marker::Copy for float4 {}

impl float4 {
    #[inspirv(intrinsic = "float4_new")]
    fn new(x: f32, y: f32, z: f32, w: f32) -> float4 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle2")]
    fn swizzle2(self, idx_x: u32, idx_y: u32) -> float2 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle3")]
    fn swizzle3(self, idx_x: u32, idx_y: u32, idx_z: u32) -> float3 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle4")]
    fn swizzle4(self, idx_x: u32, idx_y: u32, idx_z: u32, idx_w: u32) -> float4 { loop {} }
}

#[inspirv(intrinsic = "shuffle4")]
fn shuffle4(v1: float4, v2: float4, idx_x: u32, idx_y: u32, idx_z: u32, idx_w: u32) -> float4 { loop {} }

#[inspirv(interface)]
struct VertexInput {
    #[inspirv(location = 0)]
    pos: float4,
}

#[inspirv(interface)]
struct VertexVarying {
    #[inspirv(location = 0)]
    #[inspirv(builtin = "Position")]
    pos: float4,
}

#[inspirv(entry_point = "vertex")]
fn vertex(input: VertexInput) -> VertexVarying {
    let x = float4::new(0.0f32, 1.0f32, 0.0f32, 1.0f32);
    let y = x.swizzle2(0, 1);
    let z = x.swizzle2(1, 1);
    VertexVarying {
        pos: float4::new(1.0f32, 1.0f32, 0.0f32, 1.0f32),
    }
}
