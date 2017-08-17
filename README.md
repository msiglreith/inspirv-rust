# inspirv-rust

UPDATE 2: Next design iteration would probably be based on HIR instead of MIR. See more details [here](https://github.com/gfx-rs/gfx/issues/71#issuecomment-316728752) and initial work is done [here](https://github.com/msiglreith/rust/commit/1c047f4801683ee1e1dccc00b054639010d1f5e2).

UPDATE: Development currently slowed down as other projects (i.e gfx-rs) have priority over this one. Will keep on working on it in the future (see above)!

An experimental compiler from [Rust] to [SPIR-V], using the `rustc` compiler and [MIR].
The code is based upon [rustc_trans::mir], legacy (_actually working_) version was based on [miri] and [mir2wasm].

```
rustc 1.17.0-nightly (0e7727795 2017-02-19)
```

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
