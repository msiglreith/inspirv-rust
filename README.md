# inspirv-rust

An experimental compiler from [Rust] to [SPIR-V], using the `rustc` compiler and [MIR].
The code is based upon [miri] and [mir2wasm].

> rustc 1.14.0-nightly (e0111758e 2016-10-17)

## Resources

* [miri](https://github.com/solson/miri) the MIR interpreter. mir2wasm is derived
  from it but shares no actual code. It probably should share code though, and
  there's lots to learn from miri.
* [rustc_trans::mir](https://github.com/rust-lang/rust/tree/master/src/librustc_trans/mir).
* [mir2wasm](https://github.com/brson/mir2wasm)

## License

Licensed under either of
  * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
    http://www.apache.org/licenses/LICENSE-2.0)
  * MIT license ([LICENSE-MIT](LICENSE-MIT) or
    http://opensource.org/licenses/MIT) at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you shall be dual licensed as above, without any
additional terms or conditions.

[Rust]: https://www.rust-lang.org/
[MIR]: https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md
[miri]: https://github.com/solson/miri
[mir2wasm]: https://github.com/brson/mir2wasm
[SPIR-V]: https://www.khronos.org/registry/spir-v/specs/1.1/SPIRV.html
