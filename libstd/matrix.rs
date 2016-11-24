
use core::marker::Copy;
use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign};

use super::{Vector2, Vector3, Vector4};

#[derive(Copy)]
#[inspirv(matrix(rows = 2, cols = 2))]
pub struct Matrix2x2<T: Copy> {
    pub col0: Vector2<T>,
    pub col1: Vector2<T>,
}

macro_rules! matrix2x2_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Matrix2x2<$t> {
            type Output = Matrix2x2<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, rhs: Matrix2x2<$t>) -> Self::Output {
                Matrix2x2 {
                    col0: self.col0 + rhs.col0,
                    col1: self.col1 + rhs.col1,
                }
            }
        }

        impl AddAssign for Matrix2x2<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Matrix2x2<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Matrix2x2<$t> {
            type Output = Matrix2x2<$t>;

            #[inspirv(intrinsic(add))]
            fn sub(self, rhs: Matrix2x2<$t>) -> Self::Output {
                Matrix2x2 {
                    col0: self.col0 - rhs.col0,
                    col1: self.col1 - rhs.col1,
                }
            }
        }

        impl SubAssign for Matrix2x2<$t> {
            #[inline]
            fn sub_assign(&mut self, rhs: Matrix2x2<$t>) {
                *self = *self - rhs;
            }
        }

        impl Mul<$t> for Matrix2x2<$t> {
            type Output = Matrix2x2<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: $t) -> Self::Output { loop {} }
        }

        impl Mul<Matrix2x2<$t>> for $t {
            type Output = Matrix2x2<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix2x2<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Vector2<$t>> for Matrix2x2<$t> {
            type Output = Vector2<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector2<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Matrix2x2<$t>> for Matrix2x2<$t> {
            type Output = Matrix2x2<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix2x2<$t>) -> Self::Output { loop {} }
        }
    )*)
}

matrix2x2_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float2x2 = Matrix2x2<f32>;

impl Float2x2 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(self) -> Float2x2 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(self) -> Float2x2 { loop {} }
}

#[derive(Copy)]
#[inspirv(matrix(rows = 3, cols = 3))]
pub struct Matrix3x3<T: Copy> {
    pub col0: Vector3<T>,
    pub col1: Vector3<T>,
    pub col2: Vector3<T>,
}

macro_rules! matrix3x3_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Matrix3x3<$t> {
            type Output = Matrix3x3<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, _rhs: Matrix3x3<$t>) -> Self::Output { loop {} }
        }

        impl AddAssign for Matrix3x3<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Matrix3x3<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Matrix3x3<$t> {
            type Output = Matrix3x3<$t>;

            #[inspirv(intrinsic(add))]
            fn sub(self, _rhs: Matrix3x3<$t>) -> Self::Output { loop {} }
        }

        impl SubAssign for Matrix3x3<$t> {
            #[inline]
            fn sub_assign(&mut self, rhs: Matrix3x3<$t>) {
                *self = *self - rhs;
            }
        }

        impl Mul<$t> for Matrix3x3<$t> {
            type Output = Matrix3x3<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: $t) -> Self::Output { loop {} }
        }

        impl Mul<Matrix3x3<$t>> for $t {
            type Output = Matrix3x3<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix3x3<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Vector3<$t>> for Matrix3x3<$t> {
            type Output = Vector3<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector3<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Matrix3x3<$t>> for Matrix3x3<$t> {
            type Output = Matrix3x3<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix3x3<$t>) -> Self::Output { loop {} }
        }
    )*)
}

matrix3x3_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float3x3 = Matrix3x3<f32>;

impl Float3x3 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(self) -> Float3x3 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(self) -> Float3x3 { loop {} }
}

#[derive(Copy)]
#[inspirv(matrix(rows = 4, cols = 4))]
pub struct Matrix4x4<T: Copy> {
    pub col0: Vector4<T>,
    pub col1: Vector4<T>,
    pub col2: Vector4<T>,
    pub col3: Vector4<T>,
}

macro_rules! matrix4x4_ops_impl {
    ($($t:ty)*) => ($(
        impl Add for Matrix4x4<$t> {
            type Output = Matrix4x4<$t>;

            #[inspirv(intrinsic(add))]
            fn add(self, _rhs: Matrix4x4<$t>) -> Self::Output { loop {} }
        }

        impl AddAssign for Matrix4x4<$t> {
            #[inline]
            fn add_assign(&mut self, rhs: Matrix4x4<$t>) {
                *self = *self + rhs;
            }
        }

        impl Sub for Matrix4x4<$t> {
            type Output = Matrix4x4<$t>;

            #[inspirv(intrinsic(add))]
            fn sub(self, _rhs: Matrix4x4<$t>) -> Self::Output { loop {} }
        }

        impl SubAssign for Matrix4x4<$t> {
            #[inline]
            fn sub_assign(&mut self, rhs: Matrix4x4<$t>) {
                *self = *self - rhs;
            }
        }

        impl Mul<$t> for Matrix4x4<$t> {
            type Output = Matrix4x4<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: $t) -> Self::Output { loop {} }
        }

        impl Mul<Matrix4x4<$t>> for $t {
            type Output = Matrix4x4<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix4x4<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Vector4<$t>> for Matrix4x4<$t> {
            type Output = Vector4<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Vector4<$t>) -> Self::Output { loop {} }
        }

        impl Mul<Matrix4x4<$t>> for Matrix4x4<$t> {
            type Output = Matrix4x4<$t>;

            #[inspirv(intrinsic(mul))]
            fn mul(self, _rhs: Matrix4x4<$t>) -> Self::Output { loop {} }
        }
    )*)
}

matrix4x4_ops_impl! { usize u16 u32 u64 isize i16 i32 i64 f32 f64 }

pub type Float4x4 = Matrix4x4<f32>;

impl Float4x4 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(self) -> Float4x4 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(self) -> Float4x4 { loop {} }
}
