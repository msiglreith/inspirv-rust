#![feature(custom_attribute, attr_literals)]
#![allow(unused_attributes)]

struct QuadVertex {
    #[inspirv(location = 0)] pos: Float4,
    #[inspirv(location = 1)] color: Float4,
}

struct QuadVarying {
    #[inspirv(builtin = "Position")]
    #[inspirv(location = 0)] pos: Float4,
    #[inspirv(location = 1)] color: Float4,
}

struct QuadFragment {
    #[inspirv(builtin = "FragCoord")] coord: Float4,
}

struct QuadOut {
    #[inspirv(location = 0)] color: Float4,
}

#[inspirv(descriptor(set = 0, binding = 0))]
struct Locals {
    dimensions: Float2,
}

#[inspirv(entry_point = "vertex")]
fn vertex(vertex: Attributes<QuadVertex>) -> QuadVarying {
    QuadVarying {
        pos: vertex.pos,
        color: vertex.color,
    }
}

#[inspirv(entry_point = "fragment")]
fn fragment(varying: Attributes<QuadVarying>, fragment: Attributes<QuadFragment>, local: Cbuffer<Locals>) -> QuadOut {
    let w = local.dimensions.x;
    let h = local.dimensions.x;
    QuadOut {
        color: Float4::new(
            fragment.coord.x / w,
            fragment.coord.y / h,
            0.0, 1.0),
    }
}
