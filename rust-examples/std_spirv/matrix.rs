
use super::core::marker::{Copy, Sized};
use super::core::ops::Mul;

use super::{Float2, Float3, Float4};

#[inspirv(matrix(base = "f32", rows = 2, cols = 2))]
pub struct Float2x2;
impl Copy for Float2x2 {}

impl Float2x2 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(&self) -> Float2x2 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(&self) -> Float2x2 { loop {} }
}

impl Mul<f32> for Float2x2 {
    type Output = Float2x2;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: f32) -> Self::Output { loop {} }
}

impl Mul<Float2> for Float2x2 {
    type Output = Float2;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float2) -> Self::Output { loop {} }
}

impl Mul<Float2x2> for Float2x2 {
    type Output = Float2x2;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float2x2) -> Self::Output { loop {} }
}

#[inspirv(matrix(base = "f32", rows = 3, cols = 3))]
pub struct Float3x3;
impl Copy for Float3x3 {}

impl Float3x3 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(self) -> Float3x3 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(self) -> Float3x3 { loop {} }
}

impl Mul<f32> for Float3x3 {
    type Output = Float3x3;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: f32) -> Self::Output { loop {} }
}

impl Mul<Float3> for Float3x3 {
    type Output = Float3;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float3) -> Self::Output { loop {} }
}

impl Mul<Float3x3> for Float3x3 {
    type Output = Float3x3;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float3x3) -> Self::Output { loop {} }
}

#[inspirv(matrix(base = "f32", rows = 4, cols = 4))]
pub struct Float4x4;
impl Copy for Float4x4 {}

impl Float4x4 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(self) -> Float4x4 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(self) -> Float4x4 { loop {} }
}

impl Mul<f32> for Float4x4 {
    type Output = Float4x4;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: f32) -> Self::Output { loop {} }
}

impl Mul<Float4> for Float4x4 {
    type Output = Float4;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float4) -> Self::Output { loop {} }
}

impl Mul<Float4x4> for Float4x4 {
    type Output = Float4x4;

    #[inspirv(intrinsic(mul))]
    fn mul(self, _rhs: Float4x4) -> Self::Output { loop {} }
}
