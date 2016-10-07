#![crate_type = "lib"]
#![feature(fundamental, no_core, lang_items, custom_attribute, attr_literals, optin_builtin_traits)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![no_core]

mod std_spirv;
use std_spirv::*;

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
fn vertex(input: Attributes<QuadVertex>) -> QuadVarying {
    QuadVarying {
        pos: input.pos,
        color: input.color,
    }
}

#[inspirv(entry_point = "fragment")]
fn fragment(input: Attributes<QuadVarying>, fragment: Attributes<QuadFragment>, local: Cbuffer<Locals>) -> QuadOut {
    let w = local.dimensions.x;
    let h = local.dimensions.x;
    QuadOut {
        color: Float4::new(
            fragment.coord.x / w,
            fragment.coord.y / h,
            0.0, 1.0),
    }
}
