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

/*
#[inspirv(entry_point = "vertex")]
fn vertex(vertex: Attributes<QuadVertex>) -> QuadVarying {
    QuadVarying {
        pos: Float4::new(0.0, 0.0, 0.0, 1.0), //vertex.pos,
        color: Float4::new(0.0, 0.0, 0.0, 1.0), //vertex.color,
    }
}
*/

#[inspirv(entry_point = "fragment")]
fn fragment(varying: Attributes<QuadVarying>, fragment: Attributes<QuadFragment>, local: Cbuffer<Locals>) -> QuadOut {
    // let w = local.dimensions.x;
    // let h = local.dimensions.x;
    QuadOut {
        color: Float4::new(
            0.0, //fragment.coord.x / w,
            0.0, //fragment.coord.y / h,
            0.0, 1.0),
    }
}
