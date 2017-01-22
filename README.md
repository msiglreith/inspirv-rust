# inspirv-rust

An experimental compiler from [Rust] to [SPIR-V], using the `rustc` compiler and [MIR].
The code is based upon [rustc_trans::mir], legacy version was based on [miri] and [mir2wasm].

> rustc 1.15.0-nightly (daf8c1dfc 2016-12-05)

## Build
In order to build the standard and core library directly, you can run:

```
cargo run -- libcore\lib.rs --target=etc/spirv.json
cargo run -- libstd\lib.rs --extern core=libcore.rlib -L . --target=etc/spirv.json
```

To build the quad example shader:

```
cargo run -- rust-examples\quad.rs --extern std=libstd.rlib --extern core=libcore.lib -L . --target=etc/spirv.json
```

## Resources

* [miri](https://github.com/solson/miri) the MIR interpreter.
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
