#![feature(
    box_syntax,
    custom_attribute,
    rustc_private,
    slice_patterns,
    cell_extras,
)]

#![feature(plugin)]
// #![plugin(clippy)]

#[macro_use]
extern crate rustc;
extern crate rustc_borrowck;
extern crate rustc_mir;
extern crate rustc_errors;
extern crate rustc_back;
extern crate syntax;
extern crate rustc_const_math;
extern crate rustc_data_structures;
extern crate rustc_passes;
extern crate syntax_pos;
extern crate rustc_trans;
extern crate rustc_incremental;
extern crate rustc_const_eval;

extern crate arena;
extern crate libc;

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate inspirv;
extern crate inspirv_builder;

extern crate petgraph;

pub mod error;
pub mod trans;
mod attribute;
mod intrinsic;
mod monomorphize;
mod traits;

pub mod thetis;
