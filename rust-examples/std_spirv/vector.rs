
use core::marker::Copy;
use super::{Matrix2x2, Matrix3x3, Matrix4x4};

use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign};

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

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 2, num_out = 2)))]
            pub fn shuffle2x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 3, num_out = 2)))]
            pub fn shuffle2x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 4, num_out = 2)))]
            pub fn shuffle2x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 2, num_out = 3)))]
            pub fn shuffle3x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 3, num_out = 3)))]
            pub fn shuffle3x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 4, num_out = 3)))]
            pub fn shuffle3x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 2, num_out = 4)))]
            pub fn shuffle4x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 3, num_out = 4)))]
            pub fn shuffle4x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 2, num_in1 = 4, num_out = 4)))]
            pub fn shuffle4x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }
        }
    )*)
}

vector2_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 bool }

macro_rules! vector2_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Vector2<$t> {
            type Output = Vector2<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, rhs: Vector2<$t>) -> Self::Output {
                Vector2 {
                    x: self.x + rhs.x,
                    y: self.y + rhs.y,
                }
            }
        }

        impl AddAssign for Vector2<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Vector2<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Vector2<$t>  {
            type Output = Vector2<$t> ;

            #[inspirv(intrinsic(sub))]
            fn sub(self, rhs: Vector2<$t> ) -> Self::Output {
                Vector2 {
                    x: self.x - rhs.x,
                    y: self.y - rhs.y,
                }
            }
        }

        impl SubAssign for Vector2<$t>  {
            #[inline]
            fn sub_assign(&mut self, rhs: Vector2<$t> ) {
                *self = *self - rhs;
            }
        }

        impl Mul<Vector2<$t>> for $t {
            type Output= Vector2<$t>;
            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector2<$t>) -> Self::Output { loop {} }
        }
    )*)
}

vector2_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float2 = Vector2<f32>;

impl Float2 {
     #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float2) -> f32 { self.x * rhs.x + self.y * rhs.y }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float2) -> Matrix2x2<f32> { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float2 { loop {} }
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

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 2, num_out = 2)))]
            pub fn shuffle2x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 3, num_out = 2)))]
            pub fn shuffle2x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 4, num_out = 2)))]
            pub fn shuffle2x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32) -> Vector2<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 2, num_out = 3)))]
            pub fn shuffle3x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 3, num_out = 3)))]
            pub fn shuffle3x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 4, num_out = 3)))]
            pub fn shuffle3x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32) -> Vector3<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 2, num_out = 4)))]
            pub fn shuffle4x2(self, _v2: Vector2<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 3, num_out = 4)))]
            pub fn shuffle4x3(self, _v2: Vector3<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }

            #[inspirv(intrinsic(shuffle(num_in0 = 3, num_in1 = 4, num_out = 4)))]
            pub fn shuffle4x4(self, _v2: Vector4<$t>, _idx_x: u32, _idx_y: u32, _idx_z: u32, _idx_w: u32) -> Vector4<$t> { loop {} }
        }
    )*)
}

vector3_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 bool }

macro_rules! vector3_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Vector3<$t> {
            type Output = Vector3<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, rhs: Vector3<$t>) -> Self::Output {
                Vector3 {
                    x: self.x + rhs.x,
                    y: self.y + rhs.y,
                    z: self.z + rhs.z,
                }
            }
        }

        impl AddAssign for Vector3<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Vector3<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Vector3<$t> {
            type Output = Vector3<$t>;

            #[inspirv(intrinsic(sub))]
            fn sub(self, rhs: Vector3<$t>) -> Self::Output {
                Vector3 {
                    x: self.x - rhs.x,
                    y: self.y - rhs.y,
                    z: self.z - rhs.z,
                }
            }
        }

        impl SubAssign for Vector3<$t> {
            #[inline]
            fn sub_assign(&mut self, rhs: Vector3<$t>) {
                *self = *self - rhs;
            }
        }

        impl Mul<Vector3<$t>> for $t {
            type Output= Vector3<$t>;
            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector3<$t>) -> Self::Output { loop {} }
        }
    )*)
}

vector3_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float3 = Vector3<f32>;

impl Float3 {
    #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float3) -> f32 { self.x * rhs.x + self.y * rhs.y + self.z * rhs.z }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float3) -> Matrix3x3<f32> { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float3 { loop {} }

    #[inspirv(intrinsic(cross))]
    pub fn cross(self, _rhs: Float3) -> Float3 { loop {} }
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

macro_rules! vector4_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Vector4<$t> {
            type Output = Vector4<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, rhs: Vector4<$t>) -> Self::Output {
                Vector4 {
                    x: self.x + rhs.x,
                    y: self.y + rhs.y,
                    z: self.z + rhs.z,
                    w: self.w + rhs.w,
                }
            }
        }

        impl AddAssign for Vector4<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Vector4<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Vector4<$t> {
            type Output = Vector4<$t>;

            #[inspirv(intrinsic(sub))]
            fn sub(self, rhs: Vector4<$t>) -> Self::Output {
                Vector4 {
                    x: self.x - rhs.x,
                    y: self.y - rhs.y,
                    z: self.z - rhs.z,
                    w: self.w - rhs.w,
                }
            }
        }

        impl SubAssign for Vector4<$t> {
            #[inline]
            fn sub_assign(&mut self, rhs: Vector4<$t>) {
                *self = *self - rhs;
            }
        }

        impl Mul<Vector4<$t>> for $t {
            type Output = Vector4<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector4<$t>) -> Self::Output { loop {} }
        }
    )*)
}

vector4_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float4 = Vector4<f32>;

impl Float4 {
    #[inspirv(intrinsic(mul))]
    pub fn dot(self, rhs: Float4) -> f32 { self.x * rhs.x + self.y * rhs.y + self.z * rhs.z + self.w * rhs.w }

    #[inspirv(intrinsic(outer_product))]
    pub fn outer(self, _rhs: Float4) -> Matrix4x4<f32> { loop {} }

    #[inspirv(intrinsic(normalize))]
    pub fn normalize(self) -> Float4 { loop {} }
}
