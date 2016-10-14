
use super::core::marker::Copy;
use super::{Float2x2, Float3x3, Float4x4};

use super::core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign};

#[inspirv(vector(components = 2))]
pub struct Vector2<T: Copy> {
    pub x: T,
    pub y: T,
}
impl<T: Copy> Copy for Vector2<T> {}

macro_rules! vector2_impl {
    ($($t:ty)*) => ($(
        impl Vector2<$t> {
            #[inspirv(intrinsic(vector_new(1, 1)))]
            pub fn new(x: $t, y: $t) -> Vector2<$t> { Vector2 { x: x, y: y } }

            #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 2)))]
            pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 3)))]
            pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 2, num_out = 4)))]
            pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }
        }
    )*)
}

vector2_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 bool }

pub type Float2 = Vector2<f32>;

impl Float2 {
     #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float2) -> f32 { self.x * rhs.x + self.y * rhs.y }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float2) -> Float2x2 { loop {} }

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

#[inspirv(vector(components = 3))]
pub struct Vector3<T: Copy> {
    pub x: T,
    pub y: T,
    pub z: T,
}
impl<T: Copy> Copy for Vector3<T> {}

macro_rules! vector3_impl {
    ($($t:ty)*) => ($(
        impl Vector3<$t> {
            #[inspirv(intrinsic(vector_new(1, 1, 1)))]
            pub fn new(x: $t, y: $t, z: $t) -> Vector3<$t> {
                Vector3 { x: x, y: y, z: z}
            }

            #[inspirv(intrinsic(vector_new(1, 2)))]
            pub fn from_1_2(x: $t, yz: Vector2<$t>) -> Vector3<$t> {
                Vector3 { x: x, y: yz.x, z: yz.y}
            }

            #[inspirv(intrinsic(vector_new(2, 1)))]
            pub fn from_2_1(xy: Vector2<$t>, z: $t) -> Vector3<$t> {
                Vector3 { x: xy.x, y: xy.y, z: z}
            }

            #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 2)))]
            pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 3)))]
            pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 3, num_out = 4)))]
            pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }
        }
    )*)
}

vector3_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 bool }

pub type Float3 = Vector3<f32>;

impl Float3 {
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

#[inspirv(vector(components = 4))]
pub struct Vector4<T: Copy> {
    pub x: T,
    pub y: T,
    pub z: T,
    pub w: T,
}
impl<T: Copy> Copy for Vector4<T> {}

macro_rules! vector4_impl {
    ($($t:ty)*) => ($(
        impl Vector4<$t> {
            #[inspirv(intrinsic(vector_new(1, 1, 1, 1)))]
            pub fn new(x: $t, y: $t, z: $t, w: $t) -> Vector4<$t> {
                Vector4 { x: x, y: y, z: z, w: w }
            }

            #[inspirv(intrinsic(vector_new(1, 1, 2)))]
            pub fn from_1_1_2(x: $t, y: $t, zw: Vector2<$t>) -> Vector4<$t> {
                Vector4 { x: x, y: y, z: zw.x, w: zw.y }
            }

            #[inspirv(intrinsic(vector_new(1, 3)))]
            pub fn from_1_3(x: $t, yzw: Vector3<$t>) -> Vector4<$t> {
                Vector4 { x: x, y: yzw.x, z: yzw.y, w: yzw.z }
            }

            #[inspirv(intrinsic(vector_new(2, 1, 1)))]
            pub fn from_2_1_1(xy: Vector2<$t>, z: $t, w: $t) -> Vector4<$t> {
                Vector4 { x: xy.x, y: xy.y, z: z, w: w }
            }

            #[inspirv(intrinsic(vector_new(2, 2)))]
            pub fn from_2_2(xy: Vector2<$t>, zw: Vector2<$t>) -> Vector4<$t> {
                Vector4 { x: xy.x, y: xy.y, z: zw.x, w: zw.y }
            }

            #[inspirv(intrinsic(vector_new(3, 1)))]
            pub fn from_3_1(xyz: Vector3<$t>, w: $t) -> Vector4<$t> {
                Vector4 { x: xyz.x, y: xyz.y, z: xyz.z, w: w }
            }

            #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 2)))]
            pub fn swizzle2(self, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 3)))]
            pub fn swizzle3(self, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(swizzle(num_in = 4, num_out = 4)))]
            pub fn swizzle4(self, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }


            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 2)))]
            pub fn shuffle2x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 2)))]
            pub fn shuffle2x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 2)))]
            pub fn shuffle2x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 3)))]
            pub fn shuffle3x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 3)))]
            pub fn shuffle3x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 3)))]
            pub fn shuffle3x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 2, num_out = 4)))]
            pub fn shuffle4x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 3, num_out = 4)))]
            pub fn shuffle4x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 4, num_in1 = 4, num_out = 4)))]
            pub fn shuffle4x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }
        }
    )*)
}

vector4_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 bool }

pub type Float4 = Vector4<f32>;

impl Float4 {
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
