
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    Swizzle {
        components_out: u32,
        components_in: u32
    },
    Shuffle {
        components_out: u32,
        components_in0: u32,
        components_in1: u32
    },
    VectorNew(Vec<u32>),
    Add,
    Sub,
    Mul,
    Transpose,
    Inverse,
    OuterProduct,
    Normalize,
    Cross,
    Deref,
}
