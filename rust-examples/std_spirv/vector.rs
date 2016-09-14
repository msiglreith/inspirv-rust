
use super::core::marker::{Copy, Sized};

#[inspirv(vector(base = "f32", components = 2))]
pub struct Float2 {
    pub x: f32,
    pub y: f32,
}
impl Copy for Float2 {}

#[inspirv(vector(base = "f32", components = 3))]
pub struct Float3 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}
impl Copy for Float3 {}

#[inspirv(vector(base = "f32", components = 4))]
pub struct Float4 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub w: f32,
}
impl Copy for Float4 {}

impl Float4 {
    #[inspirv(intrinsic = "float4_new")]
    pub fn new(_x: f32, _y: f32, _z: f32, _w: f32) -> Float4 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle2")]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle3")]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic = "float4_swizzle4")]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }


    #[inspirv(intrinsic = "shuffle2_4x2")]
    pub fn shuffle2x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic = "shuffle2_4x3")]
    pub fn shuffle2x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic = "shuffle2_4x4")]
    pub fn shuffle2x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic = "shuffle3_4x2")]
    pub fn shuffle3x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic = "shuffle3_4x3")]
    pub fn shuffle3x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic = "shuffle3_4x4")]
    pub fn shuffle3x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic = "shuffle4_4x2")]
    pub fn shuffle4x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic = "shuffle4_4x3")]
    pub fn shuffle4x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic = "shuffle4_4x4")]
    pub fn shuffle4x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }
}
