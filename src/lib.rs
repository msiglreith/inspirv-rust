#![feature(
    box_syntax,
    custom_attribute,
    question_mark,
    rustc_private,
    slice_patterns,
)]

#![feature(plugin)]
#![plugin(clippy)]

#[macro_use]
extern crate rustc;
extern crate rustc_borrowck;
extern crate rustc_mir;
extern crate rustc_errors;
extern crate syntax;
extern crate rustc_const_math;
extern crate rustc_data_structures;
extern crate syntax_pos;

extern crate libc;

#[macro_use]
extern crate log;
extern crate env_logger;

extern crate inspirv;
extern crate inspirv_builder;

pub mod error;
pub mod trans;
mod attribute;
mod intrinsic;
mod monomorphize;
mod traits;
