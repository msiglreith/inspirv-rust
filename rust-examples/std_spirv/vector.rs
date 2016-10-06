
use super::core::marker::{Copy, Sized};
use super::{Float2x2, Float3x3, Float4x4};

use super::core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign};

#[inspirv(vector(base = "f32", components = 2))]
pub struct Float2 {
    pub x: f32,
    pub y: f32,
}
impl Copy for Float2 {}

impl Float2 {
    #[inspirv(intrinsic(vector_new(1, 1)))]
    pub fn new(_x: f32, _y: f32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 2)))]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 3)))]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 4)))]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

     #[inspirv(intrinsic(mul))]
    pub fn dot(self, _rhs: Float2) -> f32 { loop {} }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: &Float2) -> Float2x2 { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float2 { loop {} }
}

impl Add<Float2> for Float2 {
    type Output = Float2;

    #[inspirv(intrinsic(add))]
    fn add(self, _rhs: Float2) -> Self::Output { loop {} }
}


impl AddAssign<Float2> for Float2 {
    #[inline]
    fn add_assign(&mut self, rhs: Float2) {
        *self = *self + rhs;
    }
}

impl Sub<Float2> for Float2 {
    type Output = Float2;

    #[inspirv(intrinsic(sub))]
    fn sub(self, _rhs: Float2) -> Self::Output { loop {} }
}

#[inspirv(vector(base = "f32", components = 3))]
pub struct Float3 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}
impl Copy for Float3 {}

impl Float3 {
    #[inspirv(intrinsic(vector_new(1, 1, 1)))]
    pub fn new(_x: f32, _y: f32, _z: f32) -> Float3 { loop {} }

    #[inspirv(intrinsic(vector_new(1, 2)))]
    pub fn from_1_2(_x: f32, _yz: Float2) -> Float3 { loop {} }

    #[inspirv(intrinsic(vector_new(2, 1)))]
    pub fn from_2_1(_xy: Float2, _z: f32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 2)))]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 3)))]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 4)))]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic(mul))]
    pub fn dot(self, _rhs: Float3) -> f32 { loop {} }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float3) -> Float3x3 { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float3 { loop {} }

    #[inspirv(intrinsic(cross))]
    pub fn cross(self, _rhs: Float3) -> Float3 { loop {} }
}

impl Add<Float3> for Float3 {
    type Output = Float3;

    #[inspirv(intrinsic(add))]
    fn add(self, _rhs: Float3) -> Self::Output { loop {} }
}

impl Sub<Float3> for Float3 {
    type Output = Float3;

    #[inspirv(intrinsic(sub))]
    fn sub(self, _rhs: Float3) -> Self::Output { loop {} }
}

#[inspirv(vector(base = "f32", components = 4))]
pub struct Float4 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub w: f32,
}
impl Copy for Float4 {}

impl Float4 {
    #[inspirv(intrinsic(vector_new(1, 1, 1, 1)))]
    pub fn new(_x: f32, _y: f32, _z: f32, _w: f32) -> Float4 { loop {} }

    #[inspirv(intrinsic(vector_new(1, 1, 2)))]
    pub fn from_1_1_2(_x: f32, _y: f32, _zw: Float2) -> Float4 { loop {} }

    #[inspirv(intrinsic(vector_new(1, 3)))]
    pub fn from_1_3(_x: f32, _yzw: Float3) -> Float4 { loop {} }

    #[inspirv(intrinsic(vector_new(2, 1, 1)))]
    pub fn from_2_1_1(_xy: Float2, _z: f32, _w: f32) -> Float4 { loop {} }

    #[inspirv(intrinsic(vector_new(2, 2)))]
    pub fn from_2_2(_xy: Float2, _zw: Float2) -> Float4 { loop {} }

    #[inspirv(intrinsic(vector_new(3, 1)))]
    pub fn from_3_1(_xyz: Float3, _w: f32) -> Float4 { loop {} }


    #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 2)))]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 3)))]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 4)))]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }


    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 2)))]
    pub fn shuffle2x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 2)))]
    pub fn shuffle2x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 2)))]
    pub fn shuffle2x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 3)))]
    pub fn shuffle3x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 3)))]
    pub fn shuffle3x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 3)))]
    pub fn shuffle3x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 4)))]
    pub fn shuffle4x2(self, _v2: Float2, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 4)))]
    pub fn shuffle4x3(self, _v2: Float3, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 4)))]
    pub fn shuffle4x4(self, _v2: Float4, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic(mul))]
    pub fn dot(self, _rhs: Float4) -> f32 { loop {} }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float4) -> Float4x4 { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float4 { loop {} }
}

impl Add<Float4> for Float4 {
    type Output = Float4;

    #[inspirv(intrinsic(add))]
    fn add(self, _rhs: Float4) -> Self::Output { loop {} }
}

impl Sub<Float4> for Float4 {
    type Output = Float4;

    #[inspirv(intrinsic(sub))]
    fn sub(self, _rhs: Float4) -> Self::Output { loop {} }
}
