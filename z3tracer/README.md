# z3tracer

[![z3tracer on crates.io](https://img.shields.io/crates/v/z3tracer)](https://crates.io/crates/z3tracer)
[![Documentation](https://docs.rs/z3tracer/badge.svg)](https://docs.rs/z3tracer/)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

This crate provides an experimental parser for Z3 tracing logs obtained by passing
`trace=true proof=true`.

```rust
let mut model = z3tracer::Model::default();
let input = br#"
[mk-app] #0 a
[mk-app] #1 + #0 #0
[eof]
"#;
model.process(None, &input[1..])?;
assert_eq!(model.terms().len(), 2);
```

More information about Z3 tracing logs can be found in the documentation of the
project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

## Contributing

See the [CONTRIBUTING](../CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](../LICENSE-APACHE) or the [MIT
license](../LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
cargo readme | sed -e 's/\[`/`/g; s/`\]/`/g;' > README.md
-->
