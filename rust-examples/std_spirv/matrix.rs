
use super::core::marker::{Copy, Sized};

#[inspirv(matrix(base = "f32", rows = 4, cols = 4))]
pub struct Float4x4;
impl Copy for Float4x4 {}
