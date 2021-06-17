# smt2parser

[![smt2parser on crates.io](https://img.shields.io/crates/v/smt2parser)](https://crates.io/crates/smt2parser)
[![Documentation](https://docs.rs/smt2parser/badge.svg)](https://docs.rs/smt2parser/)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

This crate provides a generic parser for SMT2 commands, as specified by the
[SMT-LIB-2 standard](http://smtlib.cs.uiowa.edu/language.shtml).

Commands are parsed and immediately visited by a user-provided
implementation of the trait `visitors::Smt2Visitor`.

To obtain concrete syntax values, use `concrete::SyntaxBuilder` as a
visitor:
```rust
let input = b"(echo \"Hello world!\")(exit)";
let stream = CommandStream::new(
    &input[..],
    concrete::SyntaxBuilder,
    Some("optional/path/to/file".to_string()),
);
let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
assert!(matches!(commands[..], [
    concrete::Command::Echo {..},
    concrete::Command::Exit,
]));
assert_eq!(commands[0].to_string(), "(echo \"Hello world!\")");
```

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
