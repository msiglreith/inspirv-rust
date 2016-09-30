
use super::core::marker::{Copy, Sized};
use super::core::ops::Mul;

use super::Float4;

#[inspirv(matrix(base = "f32", rows = 4, cols = 4))]
pub struct Float4x4;
impl Copy for Float4x4 {}

impl Float4x4 {
    #[inspirv(intrinsic(transpose))]
    pub fn transpose(&self) -> Float4x4 { loop {} }

    #[inspirv(intrinsic(inverse))]
    pub fn inverse(&self) -> Float4x4 { loop {} }
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
