
use super::core::marker::Copy;
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
    pub fn new(x: f32, y: f32) -> Float2 { Float2 { x: x, y: y } }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 2)))]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 3)))]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 4)))]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

     #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float2) -> f32 { self.x * rhs.x + self.y * rhs.y }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: &Float2) -> Float2x2 { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float2 { loop {} }
}

impl Add<Float2> for Float2 {
    type Output = Float2;

    #[inspirv(intrinsic(add))]
    fn add(self, rhs: Float2) -> Self::Output {
        Float2 {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
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
    fn sub(self, rhs: Float2) -> Self::Output {
        Float2 {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

impl SubAssign<Float2> for Float2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Float2) {
        *self = *self - rhs;
    }
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
    pub fn new(x: f32, y: f32, z: f32) -> Float3 {
        Float3 { x: x, y: y, z: z}
    }

    #[inspirv(intrinsic(vector_new(1, 2)))]
    pub fn from_1_2(x: f32, yz: Float2) -> Float3 {
        Float3 { x: x, y: yz.x, z: yz.y}
    }

    #[inspirv(intrinsic(vector_new(2, 1)))]
    pub fn from_2_1(xy: Float2, z: f32) -> Float3 {
        Float3 { x: xy.x, y: xy.y, z: z}
    }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 2)))]
    pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Float2 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 3)))]
    pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Float3 { loop {} }

    #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 4)))]
    pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Float4 { loop {} }

    #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float3) -> f32 { self.x * rhs.x + self.y * rhs.y + self.z * rhs.z }

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
    fn add(self, rhs: Float3) -> Self::Output {
        Float3 {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl AddAssign<Float3> for Float3 {
    #[inline]
    fn add_assign(&mut self, rhs: Float3) {
        *self = *self + rhs;
    }
}

impl Sub<Float3> for Float3 {
    type Output = Float3;

    #[inspirv(intrinsic(sub))]
    fn sub(self, rhs: Float3) -> Self::Output {
        Float3 {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl SubAssign<Float3> for Float3 {
    #[inline]
    fn sub_assign(&mut self, rhs: Float3) {
        *self = *self - rhs;
    }
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
    pub fn new(x: f32, y: f32, z: f32, w: f32) -> Float4 {
        Float4 { x: x, y: y, z: z, w: w }
    }

    #[inspirv(intrinsic(vector_new(1, 1, 2)))]
    pub fn from_1_1_2(x: f32, y: f32, zw: Float2) -> Float4 {
        Float4 { x: x, y: y, z: zw.x, w: zw.y }
    }

    #[inspirv(intrinsic(vector_new(1, 3)))]
    pub fn from_1_3(x: f32, yzw: Float3) -> Float4 {
        Float4 { x: x, y: yzw.x, z: yzw.y, w: yzw.z }
    }

    #[inspirv(intrinsic(vector_new(2, 1, 1)))]
    pub fn from_2_1_1(xy: Float2, z: f32, w: f32) -> Float4 {
        Float4 { x: xy.x, y: xy.y, z: z, w: w }
    }

    #[inspirv(intrinsic(vector_new(2, 2)))]
    pub fn from_2_2(xy: Float2, zw: Float2) -> Float4 {
        Float4 { x: xy.x, y: xy.y, z: zw.x, w: zw.y }
    }

    #[inspirv(intrinsic(vector_new(3, 1)))]
    pub fn from_3_1(xyz: Float3, w: f32) -> Float4 {
        Float4 { x: xyz.x, y: xyz.y, z: xyz.z, w: w }
    }

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
    pub fn dot(self, rhs: Float4) -> f32 { self.x * rhs.x + self.y * rhs.y + self.z * rhs.z + self.w * rhs.w }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float4) -> Float4x4 { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float4 { loop {} }
}

impl Add<Float4> for Float4 {
    type Output = Float4;

    #[inspirv(intrinsic(add))]
    fn add(self, rhs: Float4) -> Self::Output {
        Float4 {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
            w: self.w + rhs.w,
        }
    }
}

impl AddAssign<Float4> for Float4 {
    #[inline]
    fn add_assign(&mut self, rhs: Float4) {
        *self = *self + rhs;
    }
}

impl Sub<Float4> for Float4 {
    type Output = Float4;

    #[inspirv(intrinsic(sub))]
    fn sub(self, rhs: Float4) -> Self::Output {
        Float4 {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
            w: self.w - rhs.w,
        }
    }
}

impl SubAssign<Float4> for Float4 {
    #[inline]
    fn sub_assign(&mut self, rhs: Float4) {
        *self = *self - rhs;
    }
}
